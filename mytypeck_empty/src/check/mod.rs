// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*

# check.rs

Within the check phase of type check, we check each item one at a time
(bodies of function expressions are checked as part of the containing
function).  Inference is used to supply types wherever they are
unknown.

By far the most complex case is checking the body of a function. This
can be broken down into several distinct phases:

- gather: creates type variables to represent the type of each local
  variable and pattern binding.

- main: the main pass does the lion's share of the work: it
  determines the types of all expressions, resolves
  methods, checks for most invalid conditions, and so forth.  In
  some cases, where a type is unknown, it may create a type or region
  variable and use that as the type of an expression.

  In the process of checking, various constraints will be placed on
  these type variables through the subtyping relationships requested
  through the `demand` module.  The `infer` module is in charge
  of resolving those constraints.

- regionck: after main is complete, the regionck pass goes over all
  types looking for regions and making sure that they did not escape
  into places they are not in scope.  This may also influence the
  final assignments of the various region variables if there is some
  flexibility.

- vtable: find and records the impls to use for each trait bound that
  appears on a type parameter.

- writeback: writes the final types within a function body, replacing
  type variables with their final inferred types.  These final types
  are written into the `tcx.node_types` table, which should *never* contain
  any reference to a type variable.

## Intermediate types

While type checking a function, the intermediate types for the
expressions, blocks, and so forth contained within the function are
stored in `fcx.node_types` and `fcx.item_substs`.  These types
may contain unresolved type variables.  After type checking is
complete, the functions in the writeback module are used to take the
types from this table, resolve them, and then write them into their
permanent home in the type context `ccx.tcx`.

This means that during inferencing you should use `fcx.write_ty()`
and `fcx.expr_ty()` / `fcx.node_ty()` to write/obtain the types of
nodes within the function.

The types of top-level items, which never contain unbound type
variables, are stored directly into the `tcx` tables.

n.b.: A type variable is not the same thing as a type parameter.  A
type variable is rather an "instance" of a type parameter: that is,
given a generic function `fn foo<T>(t: T)`: while checking the
function `foo`, the type `ty_param(0)` refers to the type `T`, which
is treated in abstract.  When `foo()` is called, however, `T` will be
substituted for a fresh type variable `N`.  This variable will
eventually be resolved to some concrete type (which might itself be
type parameter).

*/

pub use self::LvaluePreference::*;
pub use self::Expectation::*;
pub use self::compare_method::{compare_impl_method, compare_const_impl};
use self::TupleArgumentsFlag::*;

use astconv::{self, ast_region_to_region, ast_ty_to_ty, AstConv, PathParamMode};
use check::_match::pat_ctxt;
use fmt_macros::{Parser, Piece, Position};
use middle::astconv_util::{check_path_args, NO_TPS, NO_REGIONS};
use middle::def;
use middle::infer;
use middle::mem_categorization as mc;
use middle::mem_categorization::McResult;
use middle::pat_util::{self, pat_id_map};
use middle::privacy::{AllPublic, LastMod};
use middle::region::{self, CodeExtent};
use middle::subst::{self, Subst, Substs, VecPerParamSpace, ParamSpace, TypeSpace};
use middle::traits::{self, report_fulfillment_errors};
use middle::ty::{FnSig, GenericPredicates, TypeScheme};
use middle::ty::{Disr, ParamTy, ParameterEnvironment};
use middle::ty::{self, HasProjectionTypes, RegionEscape, ToPolyTraitRef, Ty};
use middle::ty::liberate_late_bound_regions;
use middle::ty::{MethodCall, MethodCallee, MethodMap};
use middle::ty_fold::{TypeFolder, TypeFoldable};
use rscope::RegionScope;
use session::Session;
use {CrateCtxt, lookup_full_def, require_same_types};
use TypeAndSubsts;
use lint;
use util::common::{block_query, ErrorReported, indenter, loop_query};
use util::ppaux::{self, Repr};
use util::nodemap::{DefIdMap, FnvHashMap, NodeMap};
use util::lev_distance::lev_distance;

use std::cell::{Cell, Ref, RefCell};
use std::mem::replace;
use std::iter::repeat;
use std::slice;
use syntax::{self, abi, attr};
use syntax::attr::AttrMetaMethods;
use syntax::ast::{self, DefId, Visibility};
use syntax::ast_util::{self, local_def};
use syntax::codemap::{self, Span};
use syntax::feature_gate;
use syntax::owned_slice::OwnedSlice;
use syntax::parse::token;
use syntax::print::pprust;
use syntax::ptr::P;
use syntax::visit::{self, Visitor};

mod assoc;
pub mod dropck;
pub mod _match;
pub mod writeback;
pub mod regionck;
pub mod coercion;
pub mod demand;
pub mod method;
mod upvar;
pub mod wf;
mod cast;
mod closure;
mod callee;
mod compare_method;
mod op;

/// closures defined within the function.  For example:
///
///     fn foo() {
///         bar(move|| { ... })
///     }
///
/// Here, the function `foo()` and the closure passed to
/// `bar()` will each have their own `FnCtxt`, but they will
/// share the inherited fields.
pub struct Inherited<'a, 'tcx: 'a> {
    infcx: infer::InferCtxt<'a, 'tcx>,
    locals: RefCell<NodeMap<Ty<'tcx>>>,
    param_env: ty::ParameterEnvironment<'a, 'tcx>,

    // Temporary tables:
    node_types: RefCell<NodeMap<Ty<'tcx>>>,
    item_substs: RefCell<NodeMap<ty::ItemSubsts<'tcx>>>,
    adjustments: RefCell<NodeMap<ty::AutoAdjustment<'tcx>>>,
    method_map: MethodMap<'tcx>,
    upvar_capture_map: RefCell<ty::UpvarCaptureMap>,
    closure_tys: RefCell<DefIdMap<ty::ClosureTy<'tcx>>>,
    closure_kinds: RefCell<DefIdMap<ty::ClosureKind>>,

    // A mapping from each fn's id to its signature, with all bound
    // regions replaced with free ones. Unlike the other tables, this
    // one is never copied into the tcx: it is only used by regionck.
    fn_sig_map: RefCell<NodeMap<Vec<Ty<'tcx>>>>,

    // Tracks trait obligations incurred during this function body.
    fulfillment_cx: RefCell<traits::FulfillmentContext<'tcx>>,

    // When we process a call like `c()` where `c` is a closure type,
    // we may not have decided yet whether `c` is a `Fn`, `FnMut`, or
    // `FnOnce` closure. In that case, we defer full resolution of the
    // call until upvar inference can kick in and make the
    // decision. We keep these deferred resolutions grouped by the
    // def-id of the closure, so that once we decide, we can easily go
    // back and process them.
    deferred_call_resolutions: RefCell<DefIdMap<Vec<DeferredCallResolutionHandler<'tcx>>>>,

    deferred_cast_checks: RefCell<Vec<cast::CastCheck<'tcx>>>,
}

trait DeferredCallResolution<'tcx> {
    fn resolve<'a>(&mut self, fcx: &FnCtxt<'a,'tcx>);
}

type DeferredCallResolutionHandler<'tcx> = Box<DeferredCallResolution<'tcx>+'tcx>;

/// When type-checking an expression, we propagate downward
/// whatever type hint we are able in the form of an `Expectation`.
#[derive(Copy, Clone)]
pub enum Expectation<'tcx> {
    /// We know nothing about what type this expression should have.
    NoExpectation,

    /// This expression should have the type given (or some subtype)
    ExpectHasType(Ty<'tcx>),

    /// This expression will be cast to the `Ty`
    ExpectCastableToType(Ty<'tcx>),

    /// This rvalue expression will be wrapped in `&` or `Box` and coerced
    /// to `&Ty` or `Box<Ty>`, respectively. `Ty` is `[A]` or `Trait`.
    ExpectRvalueLikeUnsized(Ty<'tcx>),
}

impl<'tcx> Expectation<'tcx> {
    // Disregard "castable to" expectations because they
    // can lead us astray. Consider for example `if cond
    // {22} else {c} as u8` -- if we propagate the
    // "castable to u8" constraint to 22, it will pick the
    // type 22u8, which is overly constrained (c might not
    // be a u8). In effect, the problem is that the
    // "castable to" expectation is not the tightest thing
    // we can say, so we want to drop it in this case.
    // The tightest thing we can say is "must unify with
    // else branch". Note that in the case of a "has type"
    // constraint, this limitation does not hold.

    // If the expected type is just a type variable, then don't use
    // an expected type. Otherwise, we might write parts of the type
    // when checking the 'then' block which are incompatible with the
    // 'else' branch.
    fn adjust_for_branches<'a>(&self, fcx: &FnCtxt<'a, 'tcx>) -> Expectation<'tcx> {
    }
}

#[derive(Copy, Clone)]
pub struct UnsafetyState {
    pub def: ast::NodeId,
    pub unsafety: ast::Unsafety,
    from_fn: bool
}

impl UnsafetyState {
    pub fn function(unsafety: ast::Unsafety, def: ast::NodeId) -> UnsafetyState {
    }

    pub fn recurse(&mut self, blk: &ast::Block) -> UnsafetyState {
    }
}

#[derive(Clone)]
pub struct FnCtxt<'a, 'tcx: 'a> {
    body_id: ast::NodeId,

    // This flag is set to true if, during the writeback phase, we encounter
    // a type error in this function.
    writeback_errors: Cell<bool>,

    // Number of errors that had been reported when we started
    // checking this function. On exit, if we find that *more* errors
    // have been reported, we will skip regionck and other work that
    // expects the types within the function to be consistent.
    err_count_on_creation: usize,

    ret_ty: ty::FnOutput<'tcx>,

    ps: RefCell<UnsafetyState>,

    inh: &'a Inherited<'a, 'tcx>,

    ccx: &'a CrateCtxt<'a, 'tcx>,
}

impl<'a, 'tcx> mc::Typer<'tcx> for FnCtxt<'a, 'tcx> {
    fn node_ty(&self, id: ast::NodeId) -> McResult<Ty<'tcx>> {
    }
    fn expr_ty_adjusted(&self, expr: &ast::Expr) -> McResult<Ty<'tcx>> {
    }
    fn type_moves_by_default(&self, span: Span, ty: Ty<'tcx>) -> bool {
    }
    fn node_method_ty(&self, method_call: ty::MethodCall)
                      -> Option<Ty<'tcx>> {
    }
    fn node_method_origin(&self, method_call: ty::MethodCall)
                          -> Option<ty::MethodOrigin<'tcx>>
    {
    }
    fn adjustments(&self) -> &RefCell<NodeMap<ty::AutoAdjustment<'tcx>>> {
    }
    fn is_method_call(&self, id: ast::NodeId) -> bool {
    }
    fn temporary_scope(&self, rvalue_id: ast::NodeId) -> Option<CodeExtent> {
    }
    fn upvar_capture(&self, upvar_id: ty::UpvarId) -> Option<ty::UpvarCapture> {
    }
}

impl<'a, 'tcx> ty::ClosureTyper<'tcx> for FnCtxt<'a, 'tcx> {
    fn param_env<'b>(&'b self) -> &'b ty::ParameterEnvironment<'b,'tcx> {
    }

    fn closure_kind(&self,
                    def_id: ast::DefId)
                    -> Option<ty::ClosureKind>
    {
    }

    fn closure_type(&self,
                    def_id: ast::DefId,
                    substs: &subst::Substs<'tcx>)
                    -> ty::ClosureTy<'tcx>
    {
    }

    fn closure_upvars(&self,
                      def_id: ast::DefId,
                      substs: &Substs<'tcx>)
                      -> Option<Vec<ty::ClosureUpvar<'tcx>>>
    {
    }
}

impl<'a, 'tcx> Inherited<'a, 'tcx> {
    fn new(tcx: &'a ty::ctxt<'tcx>,
           param_env: ty::ParameterEnvironment<'a, 'tcx>)
           -> Inherited<'a, 'tcx> {
        Inherited {
            infcx: infer::new_infer_ctxt(tcx),
            locals: RefCell::new(NodeMap()),
            param_env: param_env,
            node_types: RefCell::new(NodeMap()),
            item_substs: RefCell::new(NodeMap()),
            adjustments: RefCell::new(NodeMap()),
            method_map: RefCell::new(FnvHashMap()),
            upvar_capture_map: RefCell::new(FnvHashMap()),
            closure_tys: RefCell::new(DefIdMap()),
            closure_kinds: RefCell::new(DefIdMap()),
            fn_sig_map: RefCell::new(NodeMap()),
            fulfillment_cx: RefCell::new(traits::FulfillmentContext::new()),
            deferred_call_resolutions: RefCell::new(DefIdMap()),
            deferred_cast_checks: RefCell::new(Vec::new()),
        }
    }

    fn normalize_associated_types_in<T>(&self,
                                        typer: &ty::ClosureTyper<'tcx>,
                                        span: Span,
                                        body_id: ast::NodeId,
                                        value: &T)
                                        -> T
        where T : TypeFoldable<'tcx> + Clone + HasProjectionTypes + Repr<'tcx>
    {
    }

}

// Used by check_const and check_enum_variants
pub fn blank_fn_ctxt<'a, 'tcx>(ccx: &'a CrateCtxt<'a, 'tcx>,
                               inh: &'a Inherited<'a, 'tcx>,
                               rty: ty::FnOutput<'tcx>,
                               body_id: ast::NodeId)
                               -> FnCtxt<'a, 'tcx> {
}

fn static_inherited_fields<'a, 'tcx>(ccx: &'a CrateCtxt<'a, 'tcx>)
                                    -> Inherited<'a, 'tcx> {
}

struct CheckItemTypesVisitor<'a, 'tcx: 'a> { ccx: &'a CrateCtxt<'a, 'tcx> }
struct CheckItemBodiesVisitor<'a, 'tcx: 'a> { ccx: &'a CrateCtxt<'a, 'tcx> }

impl<'a, 'tcx> Visitor<'tcx> for CheckItemTypesVisitor<'a, 'tcx> {
    fn visit_item(&mut self, i: &'tcx ast::Item) {
    }

    fn visit_ty(&mut self, t: &'tcx ast::Ty) {
    }
}

impl<'a, 'tcx> Visitor<'tcx> for CheckItemBodiesVisitor<'a, 'tcx> {
    fn visit_item(&mut self, i: &'tcx ast::Item) {
    }
}

pub fn check_item_types(ccx: &CrateCtxt) {
}

fn check_bare_fn<'a, 'tcx>(ccx: &CrateCtxt<'a, 'tcx>,
                           decl: &'tcx ast::FnDecl,
                           body: &'tcx ast::Block,
                           fn_id: ast::NodeId,
                           fn_span: Span,
                           raw_fty: Ty<'tcx>,
                           param_env: ty::ParameterEnvironment<'a, 'tcx>)
{
}

struct GatherLocalsVisitor<'a, 'tcx: 'a> {
    fcx: &'a FnCtxt<'a, 'tcx>
}

impl<'a, 'tcx> GatherLocalsVisitor<'a, 'tcx> {
    fn assign(&mut self, _span: Span, nid: ast::NodeId, ty_opt: Option<Ty<'tcx>>) -> Ty<'tcx> {
    }
}

impl<'a, 'tcx> Visitor<'tcx> for GatherLocalsVisitor<'a, 'tcx> {
    // Add explicitly-declared locals.
    fn visit_local(&mut self, local: &'tcx ast::Local) {
    }

    // Add pattern bindings.
    fn visit_pat(&mut self, p: &'tcx ast::Pat) {
    }

    fn visit_block(&mut self, b: &'tcx ast::Block) {
    }

    // Since an expr occurs as part of the type fixed size arrays we
    // need to record the type for that node
    fn visit_ty(&mut self, t: &'tcx ast::Ty) {
    }

    // Don't descend into fns and items
    fn visit_fn(&mut self, _: visit::FnKind<'tcx>, _: &'tcx ast::FnDecl,
                _: &'tcx ast::Block, _: Span, _: ast::NodeId) { }
    fn visit_item(&mut self, _: &ast::Item) { }

}

/// Helper used by check_bare_fn and check_expr_fn. Does the grungy work of checking a function
/// body and returns the function context used for that purpose, since in the case of a fn item
/// there is still a bit more to do.
///
/// * ...
/// * inherited: other fields inherited from the enclosing fn (if any)
fn check_fn<'a, 'tcx>(ccx: &'a CrateCtxt<'a, 'tcx>,
                      unsafety: ast::Unsafety,
                      unsafety_id: ast::NodeId,
                      fn_sig: &ty::FnSig<'tcx>,
                      decl: &'tcx ast::FnDecl,
                      fn_id: ast::NodeId,
                      body: &'tcx ast::Block,
                      inherited: &'a Inherited<'a, 'tcx>)
                      -> FnCtxt<'a, 'tcx>
{
}

pub fn check_struct(ccx: &CrateCtxt, id: ast::NodeId, span: Span) {
}

pub fn check_item_type<'a,'tcx>(ccx: &CrateCtxt<'a,'tcx>, it: &'tcx ast::Item) {
}

pub fn check_item_body<'a,'tcx>(ccx: &CrateCtxt<'a,'tcx>, it: &'tcx ast::Item) {
}

fn check_trait_fn_not_const<'a,'tcx>(ccx: &CrateCtxt<'a, 'tcx>,
                                     span: Span,
                                     constness: ast::Constness)
{
}

fn check_trait_on_unimplemented<'a, 'tcx>(ccx: &CrateCtxt<'a, 'tcx>,
                               generics: &ast::Generics,
                               item: &ast::Item) {
}

/// Type checks a method body.
///
/// # Parameters
///
/// * `item_generics`: generics defined on the impl/trait that contains
///   the method
/// * `self_bound`: bound for the `Self` type parameter, if any
/// * `method`: the method definition
fn check_method_body<'a, 'tcx>(ccx: &CrateCtxt<'a, 'tcx>,
                               item_generics: &ty::Generics<'tcx>,
                               sig: &'tcx ast::MethodSig,
                               body: &'tcx ast::Block,
                               id: ast::NodeId, span: Span) {
}

fn check_impl_items_against_trait<'a, 'tcx>(ccx: &CrateCtxt<'a, 'tcx>,
                                            impl_span: Span,
                                            impl_trait_ref: &ty::TraitRef<'tcx>,
                                            impl_items: &[P<ast::ImplItem>]) {
}

fn report_cast_to_unsized_type<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                         span: Span,
                                         t_span: Span,
                                         e_span: Span,
                                         t_cast: Ty<'tcx>,
                                         t_expr: Ty<'tcx>,
                                         id: ast::NodeId) {
}


impl<'a, 'tcx> AstConv<'tcx> for FnCtxt<'a, 'tcx> {
    fn tcx(&self) -> &ty::ctxt<'tcx> { self.ccx.tcx }

    fn get_item_type_scheme(&self, _: Span, id: ast::DefId)
                            -> Result<ty::TypeScheme<'tcx>, ErrorReported>
    {
    }

    fn get_trait_def(&self, _: Span, id: ast::DefId)
                     -> Result<&'tcx ty::TraitDef<'tcx>, ErrorReported>
    {
    }

    fn ensure_super_predicates(&self, _: Span, _: ast::DefId) -> Result<(), ErrorReported> {
    }

    fn get_free_substs(&self) -> Option<&Substs<'tcx>> {
    }

    fn get_type_parameter_bounds(&self,
                                 _: Span,
                                 node_id: ast::NodeId)
                                 -> Result<Vec<ty::PolyTraitRef<'tcx>>, ErrorReported>
    {
    }

    fn trait_defines_associated_type_named(&self,
                                           trait_def_id: ast::DefId,
                                           assoc_name: ast::Name)
                                           -> bool
    {
    }

    fn ty_infer(&self, _span: Span) -> Ty<'tcx> {
    }

    fn projected_ty_from_poly_trait_ref(&self,
                                        span: Span,
                                        poly_trait_ref: ty::PolyTraitRef<'tcx>,
                                        item_name: ast::Name)
                                        -> Ty<'tcx>
    {
    }

    fn projected_ty(&self,
                    span: Span,
                    trait_ref: ty::TraitRef<'tcx>,
                    item_name: ast::Name)
                    -> Ty<'tcx>
    {
    }
}

impl<'a, 'tcx> FnCtxt<'a, 'tcx> {
    fn tcx(&self) -> &ty::ctxt<'tcx> { self.ccx.tcx }

    pub fn infcx(&self) -> &infer::InferCtxt<'a,'tcx> {
    }

    pub fn param_env(&self) -> &ty::ParameterEnvironment<'a,'tcx> {
    }

    pub fn sess(&self) -> &Session {
    }

    pub fn err_count_since_creation(&self) -> usize {
    }

    /// Resolves type variables in `ty` if possible. Unlike the infcx
    /// version, this version will also select obligations if it seems
    /// useful, in an effort to get more type information.
    fn resolve_type_vars_if_possible(&self, mut ty: Ty<'tcx>) -> Ty<'tcx> {
    }

    /// Resolves all type variables in `t` and then, if any were left
    /// unresolved, substitutes an error type. This is used after the
    /// main checking when doing a second pass before writeback. The
    /// justification is that writeback will produce an error for
    /// these unconstrained type variables.
    fn resolve_type_vars_or_error(&self, t: &Ty<'tcx>) -> mc::McResult<Ty<'tcx>> {
    }

    fn record_deferred_call_resolution(&self,
                                       closure_def_id: ast::DefId,
                                       r: DeferredCallResolutionHandler<'tcx>) {
    }

    fn remove_deferred_call_resolutions(&self,
                                        closure_def_id: ast::DefId)
                                        -> Vec<DeferredCallResolutionHandler<'tcx>>
    {
    }

    pub fn tag(&self) -> String {
    }

    pub fn local_ty(&self, span: Span, nid: ast::NodeId) -> Ty<'tcx> {
    }

    /// Apply "fallbacks" to some types
    /// ! gets replaced with (), unconstrained ints with i32, and unconstrained floats with f64.
    pub fn default_type_parameters(&self) {
    }

    #[inline]
    pub fn write_ty(&self, node_id: ast::NodeId, ty: Ty<'tcx>) {
    }

    pub fn write_substs(&self, node_id: ast::NodeId, substs: ty::ItemSubsts<'tcx>) {
    }

    pub fn write_autoderef_adjustment(&self,
                                      node_id: ast::NodeId,
                                      derefs: usize) {
    }

    pub fn write_adjustment(&self,
                            node_id: ast::NodeId,
                            adj: ty::AutoAdjustment<'tcx>) {
    }

    /// Basically whenever we are converting from a type scheme into
    /// the fn body space, we always want to normalize associated
    /// types as well. This function combines the two.
    fn instantiate_type_scheme<T>(&self,
                                  span: Span,
                                  substs: &Substs<'tcx>,
                                  value: &T)
                                  -> T
        where T : TypeFoldable<'tcx> + Clone + HasProjectionTypes + Repr<'tcx>
    {
    }

    /// As `instantiate_type_scheme`, but for the bounds found in a
    /// generic type scheme.
    fn instantiate_bounds(&self,
                          span: Span,
                          substs: &Substs<'tcx>,
                          bounds: &ty::GenericPredicates<'tcx>)
                          -> ty::InstantiatedPredicates<'tcx>
    {
    }


    fn normalize_associated_types_in<T>(&self, span: Span, value: &T) -> T
        where T : TypeFoldable<'tcx> + Clone + HasProjectionTypes + Repr<'tcx>
    {
    }

    fn normalize_associated_type(&self,
                                 span: Span,
                                 trait_ref: ty::TraitRef<'tcx>,
                                 item_name: ast::Name)
                                 -> Ty<'tcx>
    {
    }

    /// Returns the type of `def_id` with all generics replaced by by fresh type/region variables.
    /// Also returns the substitution from the type parameters on `def_id` to the fresh variables.
    /// Registers any trait obligations specified on `def_id` at the same time.
    ///
    /// Note that function is only intended to be used with types (notably, not fns). This is
    /// because it doesn't do any instantiation of late-bound regions.
    pub fn instantiate_type(&self,
                            span: Span,
                            def_id: ast::DefId)
                            -> TypeAndSubsts<'tcx>
    {
    }

    /// Returns the type that this AST path refers to. If the path has no type
    /// parameters and the corresponding type has type parameters, fresh type
    /// and/or region variables are substituted.
    ///
    /// This is used when checking the constructor in struct literals.
    fn instantiate_struct_literal_ty(&self,
                                     did: ast::DefId,
                                     path: &ast::Path)
                                     -> TypeAndSubsts<'tcx>
    {
    }

    pub fn write_nil(&self, node_id: ast::NodeId) {
    }
    pub fn write_error(&self, node_id: ast::NodeId) {
    }

    pub fn require_type_meets(&self,
                              ty: Ty<'tcx>,
                              span: Span,
                              code: traits::ObligationCauseCode<'tcx>,
                              bound: ty::BuiltinBound)
    {
    }

    pub fn require_type_is_sized(&self,
                                 ty: Ty<'tcx>,
                                 span: Span,
                                 code: traits::ObligationCauseCode<'tcx>)
    {
    }

    pub fn require_expr_have_sized_type(&self,
                                        expr: &ast::Expr,
                                        code: traits::ObligationCauseCode<'tcx>)
    {
    }

    pub fn type_is_known_to_be_sized(&self,
                                     ty: Ty<'tcx>,
                                     span: Span)
                                     -> bool
    {
    }

    pub fn register_builtin_bound(&self,
                                  ty: Ty<'tcx>,
                                  builtin_bound: ty::BuiltinBound,
                                  cause: traits::ObligationCause<'tcx>)
    {
    }

    pub fn register_predicate(&self,
                              obligation: traits::PredicateObligation<'tcx>)
    {
    }

    pub fn to_ty(&self, ast_t: &ast::Ty) -> Ty<'tcx> {
    }

    pub fn pat_to_string(&self, pat: &ast::Pat) -> String {
    }

    pub fn expr_ty(&self, ex: &ast::Expr) -> Ty<'tcx> {
    }

    /// Apply `adjustment` to the type of `expr`
    pub fn adjust_expr_ty(&self,
                          expr: &ast::Expr,
                          adjustment: Option<&ty::AutoAdjustment<'tcx>>)
                          -> Ty<'tcx>
    {
    }

    pub fn node_ty(&self, id: ast::NodeId) -> Ty<'tcx> {
    }

    pub fn item_substs(&self) -> Ref<NodeMap<ty::ItemSubsts<'tcx>>> {
    }

    pub fn opt_node_ty_substs<F>(&self,
                                 id: ast::NodeId,
                                 f: F) where
        F: FnOnce(&ty::ItemSubsts<'tcx>),
    {
    }

    pub fn mk_subty(&self,
                    a_is_expected: bool,
                    origin: infer::TypeOrigin,
                    sub: Ty<'tcx>,
                    sup: Ty<'tcx>)
                    -> Result<(), ty::type_err<'tcx>> {
                    }

    pub fn mk_eqty(&self,
                   a_is_expected: bool,
                   origin: infer::TypeOrigin,
                   sub: Ty<'tcx>,
                   sup: Ty<'tcx>)
                   -> Result<(), ty::type_err<'tcx>> {
    }

    pub fn mk_subr(&self,
                   origin: infer::SubregionOrigin<'tcx>,
                   sub: ty::Region,
                   sup: ty::Region) {
    }

    pub fn type_error_message<M>(&self,
                                 sp: Span,
                                 mk_msg: M,
                                 actual_ty: Ty<'tcx>,
                                 err: Option<&ty::type_err<'tcx>>) where
        M: FnOnce(String) -> String,
    {
    }

    pub fn report_mismatched_types(&self,
                                   sp: Span,
                                   e: Ty<'tcx>,
                                   a: Ty<'tcx>,
                                   err: &ty::type_err<'tcx>) {
    }

    /// Registers an obligation for checking later, during regionck, that the type `ty` must
    /// outlive the region `r`.
    pub fn register_region_obligation(&self,
                                      ty: Ty<'tcx>,
                                      region: ty::Region,
                                      cause: traits::ObligationCause<'tcx>)
    {
    }

    pub fn add_default_region_param_bounds(&self,
                                           substs: &Substs<'tcx>,
                                           expr: &ast::Expr)
    {
    }

    /// Given a fully substituted set of bounds (`generic_bounds`), and the values with which each
    /// type/region parameter was instantiated (`substs`), creates and registers suitable
    /// trait/region obligations.
    ///
    /// For example, if there is a function:
    ///
    /// ```
    /// fn foo<'a,T:'a>(...)
    /// ```
    ///
    /// and a reference:
    ///
    /// ```
    /// let f = foo;
    /// ```
    ///
    /// Then we will create a fresh region variable `'$0` and a fresh type variable `$1` for `'a`
    /// and `T`. This routine will add a region obligation `$1:'$0` and register it locally.
    pub fn add_obligations_for_parameters(&self,
                                          cause: traits::ObligationCause<'tcx>,
                                          predicates: &ty::InstantiatedPredicates<'tcx>)
    {
    }

    // Only for fields! Returns <none> for methods>
    // Indifferent to privacy flags
    pub fn lookup_field_ty(&self,
                           span: Span,
                           class_id: ast::DefId,
                           items: &[ty::field_ty],
                           fieldname: ast::Name,
                           substs: &subst::Substs<'tcx>)
                           -> Option<Ty<'tcx>>
    {
    }

    pub fn lookup_tup_field_ty(&self,
                               span: Span,
                               class_id: ast::DefId,
                               items: &[ty::field_ty],
                               idx: usize,
                               substs: &subst::Substs<'tcx>)
                               -> Option<Ty<'tcx>>
    {
    }

    fn check_casts(&self) {
    }

    fn select_all_obligations_and_apply_defaults(&self) {
    }

    fn select_all_obligations_or_error(&self) {
    }

    /// Select as many obligations as we can at present.
    fn select_obligations_where_possible(&self) {
    }

    /// Try to select any fcx obligation that we haven't tried yet, in an effort
    /// to improve inference. You could just call
    /// `select_obligations_where_possible` except that it leads to repeated
    /// work.
    fn select_new_obligations(&self) {
    }

}

impl<'a, 'tcx> RegionScope for FnCtxt<'a, 'tcx> {
    fn object_lifetime_default(&self, span: Span) -> Option<ty::Region> {
    }

    fn anon_regions(&self, span: Span, count: usize)
                    -> Result<Vec<ty::Region>, Option<Vec<(String, usize)>>> {
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LvaluePreference {
    PreferMutLvalue,
    NoPreference
}

/// Whether `autoderef` requires types to resolve.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum UnresolvedTypeAction {
    /// Produce an error and return `ty_err` whenever a type cannot
    /// be resolved (i.e. it is `ty_infer`).
    Error,
    /// Go on without emitting any errors, and return the unresolved
    /// type. Useful for probing, e.g. in coercions.
    Ignore
}

/// Executes an autoderef loop for the type `t`. At each step, invokes `should_stop` to decide
/// whether to terminate the loop. Returns the final type and number of derefs that it performed.
///
/// Note: this method does not modify the adjustments table. The caller is responsible for
/// inserting an AutoAdjustment record into the `fcx` using one of the suitable methods.
pub fn autoderef<'a, 'tcx, T, F>(fcx: &FnCtxt<'a, 'tcx>,
                                 sp: Span,
                                 base_ty: Ty<'tcx>,
                                 opt_expr: Option<&ast::Expr>,
                                 unresolved_type_action: UnresolvedTypeAction,
                                 mut lvalue_pref: LvaluePreference,
                                 mut should_stop: F)
                                 -> (Ty<'tcx>, usize, Option<T>)
    where F: FnMut(Ty<'tcx>, usize) -> Option<T>,
{
}

fn try_overloaded_deref<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                  span: Span,
                                  method_call: Option<MethodCall>,
                                  base_expr: Option<&ast::Expr>,
                                  base_ty: Ty<'tcx>,
                                  lvalue_pref: LvaluePreference)
                                  -> Option<ty::mt<'tcx>>
{
}

/// For the overloaded lvalue expressions (`*x`, `x[3]`), the trait returns a type of `&T`, but the
/// actual type we assign to the *expression* is `T`. So this function just peels off the return
/// type by one layer to yield `T`. It also inserts the `method-callee` into the method map.
fn make_overloaded_lvalue_return_type<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                                method_call: Option<MethodCall>,
                                                method: Option<MethodCallee<'tcx>>)
                                                -> Option<ty::mt<'tcx>>
{
}

fn lookup_indexing<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                             expr: &ast::Expr,
                             base_expr: &'tcx ast::Expr,
                             base_ty: Ty<'tcx>,
                             idx_ty: Ty<'tcx>,
                             lvalue_pref: LvaluePreference)
                             -> Option<(/*index type*/ Ty<'tcx>, /*element type*/ Ty<'tcx>)>
{
}

/// To type-check `base_expr[index_expr]`, we progressively autoderef (and otherwise adjust)
/// `base_expr`, looking for a type which either supports builtin indexing or overloaded indexing.
/// This loop implements one step in that search; the autoderef loop is implemented by
/// `lookup_indexing`.
fn try_index_step<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                            method_call: MethodCall,
                            expr: &ast::Expr,
                            base_expr: &'tcx ast::Expr,
                            adjusted_ty: Ty<'tcx>,
                            autoderefs: usize,
                            unsize: bool,
                            lvalue_pref: LvaluePreference,
                            index_ty: Ty<'tcx>)
                            -> Option<(/*index type*/ Ty<'tcx>, /*element type*/ Ty<'tcx>)>
{
}

fn check_method_argument_types<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                         sp: Span,
                                         method_fn_ty: Ty<'tcx>,
                                         callee_expr: &'tcx ast::Expr,
                                         args_no_rcvr: &'tcx [P<ast::Expr>],
                                         tuple_arguments: TupleArgumentsFlag,
                                         expected: Expectation<'tcx>)
                                         -> ty::FnOutput<'tcx> {
}

/// Generic function that factors out common logic from function calls, method calls and overloaded
/// operators.
fn check_argument_types<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                  sp: Span,
                                  fn_inputs: &[Ty<'tcx>],
                                  expected_arg_tys: &[Ty<'tcx>],
                                  args: &'tcx [P<ast::Expr>],
                                  variadic: bool,
                                  tuple_arguments: TupleArgumentsFlag) {
}

// FIXME(#17596) Ty<'tcx> is incorrectly invariant w.r.t 'tcx.
fn err_args<'tcx>(tcx: &ty::ctxt<'tcx>, len: usize) -> Vec<Ty<'tcx>> {
}

fn write_call<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                        call_expr: &ast::Expr,
                        output: ty::FnOutput<'tcx>) {
}

// AST fragment checking
fn check_lit<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                       lit: &ast::Lit,
                       expected: Expectation<'tcx>)
                       -> Ty<'tcx>
{
}

pub fn check_expr_has_type<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                     expr: &'tcx ast::Expr,
                                     expected: Ty<'tcx>) {
}

fn check_expr_coercable_to_type<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                          expr: &'tcx ast::Expr,
                                          expected: Ty<'tcx>) {
}

fn check_expr_with_hint<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, expr: &'tcx ast::Expr,
                                  expected: Ty<'tcx>) {
}

fn check_expr_with_expectation<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                         expr: &'tcx ast::Expr,
                                         expected: Expectation<'tcx>) {
}

fn check_expr_with_expectation_and_lvalue_pref<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                                         expr: &'tcx ast::Expr,
                                                         expected: Expectation<'tcx>,
                                                         lvalue_pref: LvaluePreference)
{
}

fn check_expr<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>, expr: &'tcx ast::Expr)  {
}

fn check_expr_with_lvalue_pref<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>, expr: &'tcx ast::Expr,
                                        lvalue_pref: LvaluePreference)  {
}

// determine the `self` type, using fresh variables for all variables
// declared on the impl declaration e.g., `impl<A,B> for Vec<(A,B)>`
// would return ($0, $1) where $0 and $1 are freshly instantiated type
// variables.
pub fn impl_self_ty<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                              span: Span, // (potential) receiver for this impl
                              did: ast::DefId)
                              -> TypeAndSubsts<'tcx> {
}

/// Controls whether the arguments are tupled. This is used for the call
/// operator.
///
/// Tupling means that all call-side arguments are packed into a tuple and
/// passed as a single parameter. For example, if tupling is enabled, this
/// function:
///
///     fn f(x: (isize, isize))
///
/// Can be called as:
///
///     f(1, 2);
///
/// Instead of:
///
///     f((1, 2));
#[derive(Clone, Eq, PartialEq)]
enum TupleArgumentsFlag {
    DontTupleArguments,
    TupleArguments,
}

/// Unifies the return type with the expected type early, for more coercions
/// and forward type information on the argument expressions.
fn expected_types_for_fn_args<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                        call_span: Span,
                                        expected_ret: Expectation<'tcx>,
                                        formal_ret: ty::FnOutput<'tcx>,
                                        formal_args: &[Ty<'tcx>])
                                        -> Vec<Ty<'tcx>> {
}

/// Invariant:
/// If an expression has any sub-expressions that result in a type error,
/// inspecting that expression's type with `ty::type_is_error` will return
/// true. Likewise, if an expression is known to diverge, inspecting its
/// type with `ty::type_is_bot` will return true (n.b.: since Rust is
/// strict, _|_ can appear in the type of an expression that does not,
/// itself, diverge: for example, fn() -> _|_.)
/// Note that inspecting a type's structure *directly* may expose the fact
/// that there are actually multiple representations for `ty_err`, so avoid
/// that when err needs to be handled differently.
fn check_expr_with_unifier<'a, 'tcx, F>(fcx: &FnCtxt<'a, 'tcx>,
                                        expr: &'tcx ast::Expr,
                                        expected: Expectation<'tcx>,
                                        lvalue_pref: LvaluePreference,
                                        unifier: F) where
    F: FnOnce(),
{
}

pub fn resolve_ty_and_def_ufcs<'a, 'b, 'tcx>(fcx: &FnCtxt<'b, 'tcx>,
                                             path_res: def::PathResolution,
                                             opt_self_ty: Option<Ty<'tcx>>,
                                             path: &'a ast::Path,
                                             span: Span,
                                             node_id: ast::NodeId)
                                             -> Option<(Option<Ty<'tcx>>,
                                                        &'a [ast::PathSegment],
                                                        def::Def)>
{
}

fn constrain_path_type_parameters(fcx: &FnCtxt,
                                  expr: &ast::Expr)
{
}

impl<'tcx> Expectation<'tcx> {
    /// Provide an expectation for an rvalue expression given an *optional*
    /// hint, which is not required for type safety (the resulting type might
    /// be checked higher up, as is the case with `&expr` and `box expr`), but
    /// is useful in determining the concrete type.
    ///
    /// The primary use case is where the expected type is a fat pointer,
    /// like `&[isize]`. For example, consider the following statement:
    ///
    ///    let x: &[isize] = &[1, 2, 3];
    ///
    /// In this case, the expected type for the `&[1, 2, 3]` expression is
    /// `&[isize]`. If however we were to say that `[1, 2, 3]` has the
    /// expectation `ExpectHasType([isize])`, that would be too strong --
    /// `[1, 2, 3]` does not have the type `[isize]` but rather `[isize; 3]`.
    /// It is only the `&[1, 2, 3]` expression as a whole that can be coerced
    /// to the type `&[isize]`. Therefore, we propagate this more limited hint,
    /// which still is useful, because it informs integer literals and the like.
    /// See the test case `test/run-pass/coerce-expect-unsized.rs` and #20169
    /// for examples of where this comes up,.
    fn rvalue_hint(ty: Ty<'tcx>) -> Expectation<'tcx> {
    }

    // Resolves `expected` by a single level if it is a variable. If
    // there is no expected type or resolution is not possible (e.g.,
    // no constraints yet present), just returns `None`.
    fn resolve<'a>(self, fcx: &FnCtxt<'a, 'tcx>) -> Expectation<'tcx> {
    }

    fn to_option<'a>(self, fcx: &FnCtxt<'a, 'tcx>) -> Option<Ty<'tcx>> {
    }

    fn only_has_type<'a>(self, fcx: &FnCtxt<'a, 'tcx>) -> Option<Ty<'tcx>> {
    }
}

impl<'tcx> Repr<'tcx> for Expectation<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
    }
}

pub fn check_decl_initializer<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                                       local: &'tcx ast::Local,
                                       init: &'tcx ast::Expr)
{
}

pub fn check_decl_local<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>, local: &'tcx ast::Local)  {
}

pub fn check_block_no_value<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>, blk: &'tcx ast::Block)  {
}

fn check_block_with_expected<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                       blk: &'tcx ast::Block,
                                       expected: Expectation<'tcx>) {
}

/// Checks a constant appearing in a type. At the moment this is just the
/// length expression in a fixed-length vector, but someday it might be
/// extended to type-level numeric literals.
fn check_const_in_type<'a,'tcx>(ccx: &'a CrateCtxt<'a,'tcx>,
                                expr: &'tcx ast::Expr,
                                expected_type: Ty<'tcx>) {
}

fn check_const<'a,'tcx>(ccx: &CrateCtxt<'a,'tcx>,
                        sp: Span,
                        e: &'tcx ast::Expr,
                        id: ast::NodeId) {
}

fn check_const_with_ty<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                 _: Span,
                                 e: &'tcx ast::Expr,
                                 declty: Ty<'tcx>) {
}

/// Checks whether a type can be represented in memory. In particular, it
/// identifies types that contain themselves without indirection through a
/// pointer, which would mean their size is unbounded. This is different from
/// the question of whether a type can be instantiated. See the definition of
/// `check_instantiable`.
pub fn check_representable(tcx: &ty::ctxt,
                           sp: Span,
                           item_id: ast::NodeId,
                           designation: &str) -> bool {
}

/// Checks whether a type can be created without an instance of itself.
/// This is similar but different from the question of whether a type
/// can be represented.  For example, the following type:
///
///     enum foo { None, Some(foo) }
///
/// is instantiable but is not representable.  Similarly, the type
///
///     enum foo { Some(@foo) }
///
/// is representable, but not instantiable.
pub fn check_instantiable(tcx: &ty::ctxt,
                          sp: Span,
                          item_id: ast::NodeId)
                          -> bool {
}

pub fn check_simd(tcx: &ty::ctxt, sp: Span, id: ast::NodeId) {
}

pub fn check_enum_variants<'a,'tcx>(ccx: &CrateCtxt<'a,'tcx>,
                                    sp: Span,
                                    vs: &'tcx [P<ast::Variant>],
                                    id: ast::NodeId) {
}

// Returns the type parameter count and the type for the given definition.
fn type_scheme_and_predicates_for_def<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                                sp: Span,
                                                defn: def::Def)
                                                -> (TypeScheme<'tcx>, GenericPredicates<'tcx>) {
}

// Instantiates the given path, which must refer to an item with the given
// number of type parameters and type.
pub fn instantiate_path<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                  segments: &[ast::PathSegment],
                                  type_scheme: TypeScheme<'tcx>,
                                  type_predicates: &ty::GenericPredicates<'tcx>,
                                  opt_self_ty: Option<Ty<'tcx>>,
                                  def: def::Def,
                                  span: Span,
                                  node_id: ast::NodeId) {
}

fn structurally_resolve_type_or_else<'a, 'tcx, F>(fcx: &FnCtxt<'a, 'tcx>,
                                                  sp: Span,
                                                  ty: Ty<'tcx>,
                                                  f: F) -> Ty<'tcx>
    where F: Fn() -> Ty<'tcx>
{
}

// Resolves `typ` by a single level if `typ` is a type variable.  If no
// resolution is possible, then an error is reported.
pub fn structurally_resolved_type<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                            sp: Span,
                                            ty: Ty<'tcx>)
                                            -> Ty<'tcx>
{
}

// Returns true if b contains a break that can exit from b
pub fn may_break(cx: &ty::ctxt, id: ast::NodeId, b: &ast::Block) -> bool {
}

pub fn check_bounds_are_used<'a, 'tcx>(ccx: &CrateCtxt<'a, 'tcx>,
                                       span: Span,
                                       tps: &OwnedSlice<ast::TyParam>,
                                       ty: Ty<'tcx>) {
}

/// Remember to add all intrinsics here, in librustc_trans/trans/intrinsic.rs,
/// and in libcore/intrinsics.rs
pub fn check_intrinsic_type(ccx: &CrateCtxt, it: &ast::ForeignItem) {
}

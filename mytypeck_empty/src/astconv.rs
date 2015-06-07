// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Conversion from AST representation of types to the ty.rs
//! representation.  The main routine here is `ast_ty_to_ty()`: each use
//! is parameterized by an instance of `AstConv` and a `RegionScope`.
//!
//! The parameterization of `ast_ty_to_ty()` is because it behaves
//! somewhat differently during the collect and check phases,
//! particularly with respect to looking up the types of top-level
//! items.  In the collect phase, the crate context is used as the
//! `AstConv` instance; in this phase, the `get_item_type_scheme()`
//! function triggers a recursive call to `type_scheme_of_item()`
//! (note that `ast_ty_to_ty()` will detect recursive types and report
//! an error).  In the check phase, when the FnCtxt is used as the
//! `AstConv`, `get_item_type_scheme()` just looks up the item type in
//! `tcx.tcache` (using `ty::lookup_item_type`).
//!
//! The `RegionScope` trait controls what happens when the user does
//! not specify a region in some location where a region is required
//! (e.g., if the user writes `&Foo` as a type rather than `&'a Foo`).
//! See the `rscope` module for more details.
//!
//! Unlike the `AstConv` trait, the region scope can change as we descend
//! the type.  This is to accommodate the fact that (a) fn types are binding
//! scopes and (b) the default region may change.  To understand case (a),
//! consider something like:
//!
//!   type foo = { x: &a.int, y: |&a.int| }
//!
//! The type of `x` is an error because there is no region `a` in scope.
//! In the type of `y`, however, region `a` is considered a bound region
//! as it does not already appear in scope.
//!
//! Case (b) says that if you have a type:
//!   type foo<'a> = ...;
//!   type bar = fn(&foo, &a.foo)
//! The fully expanded version of type bar is:
//!   type bar = fn(&'foo &, &a.foo<'a>)
//! Note that the self region for the `foo` defaulted to `&` in the first
//! case but `&a` in the second.  Basically, defaults that appear inside
//! an rptr (`&r.T`) use the region `r` that appears in the rptr.

use middle::astconv_util::{prim_ty_to_ty, check_path_args, NO_TPS, NO_REGIONS};
use middle::const_eval;
use middle::def;
use middle::implicator::object_region_bounds;
use middle::resolve_lifetime as rl;
use middle::privacy::{AllPublic, LastMod};
use middle::subst::{FnSpace, TypeSpace, SelfSpace, Subst, Substs};
use middle::traits;
use middle::ty::{self, RegionEscape, Ty};
use rscope::{self, UnelidableRscope, RegionScope, ElidableRscope, ExplicitRscope,
             ObjectLifetimeDefaultRscope, ShiftedRscope, BindingRscope};
use util::common::{ErrorReported, FN_OUTPUT_NAME};
use util::nodemap::FnvHashSet;
use util::ppaux::{self, Repr, UserString};

use std::iter::repeat;
use std::slice;
use syntax::{abi, ast, ast_util};
use syntax::codemap::{Span, Pos};
use syntax::parse::token;
use syntax::print::pprust;

pub trait AstConv<'tcx> {
    fn tcx<'a>(&'a self) -> &'a ty::ctxt<'tcx>;

    /// Identify the type scheme for an item with a type, like a type
    /// alias, fn, or struct. This allows you to figure out the set of
    /// type parameters defined on the item.
    fn get_item_type_scheme(&self, span: Span, id: ast::DefId)
                            -> Result<ty::TypeScheme<'tcx>, ErrorReported>;

    /// Returns the `TraitDef` for a given trait. This allows you to
    /// figure out the set of type parameters defined on the trait.
    fn get_trait_def(&self, span: Span, id: ast::DefId)
                     -> Result<&'tcx ty::TraitDef<'tcx>, ErrorReported>;

    /// Ensure that the super-predicates for the trait with the given
    /// id are available and also for the transitive set of
    /// super-predicates.
    fn ensure_super_predicates(&self, span: Span, id: ast::DefId)
                               -> Result<(), ErrorReported>;

    /// Returns the set of bounds in scope for the type parameter with
    /// the given id.
    fn get_type_parameter_bounds(&self, span: Span, def_id: ast::NodeId)
                                 -> Result<Vec<ty::PolyTraitRef<'tcx>>, ErrorReported>;

    /// Returns true if the trait with id `trait_def_id` defines an
    /// associated type with the name `name`.
    fn trait_defines_associated_type_named(&self, trait_def_id: ast::DefId, name: ast::Name)
                                           -> bool;

    /// Return an (optional) substitution to convert bound type parameters that
    /// are in scope into free ones. This function should only return Some
    /// within a fn body.
    /// See ParameterEnvironment::free_substs for more information.
    fn get_free_substs(&self) -> Option<&Substs<'tcx>> {
    }

    /// What type should we use when a type is omitted?
    fn ty_infer(&self, span: Span) -> Ty<'tcx>;

    /// Projecting an associated type from a (potentially)
    /// higher-ranked trait reference is more complicated, because of
    /// the possibility of late-bound regions appearing in the
    /// associated type binding. This is not legal in function
    /// signatures for that reason. In a function body, we can always
    /// handle it because we can use inference variables to remove the
    /// late-bound regions.
    fn projected_ty_from_poly_trait_ref(&self,
                                        span: Span,
                                        poly_trait_ref: ty::PolyTraitRef<'tcx>,
                                        item_name: ast::Name)
                                        -> Ty<'tcx>
    {
    }

    /// Project an associated type from a non-higher-ranked trait reference.
    /// This is fairly straightforward and can be accommodated in any context.
    fn projected_ty(&self,
                    span: Span,
                    _trait_ref: ty::TraitRef<'tcx>,
                    _item_name: ast::Name)
                    -> Ty<'tcx>;
}

pub fn ast_region_to_region(tcx: &ty::ctxt, lifetime: &ast::Lifetime)
                            -> ty::Region {
}

pub fn opt_ast_region_to_region<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    default_span: Span,
    opt_lifetime: &Option<ast::Lifetime>) -> ty::Region
{
}

/// Given a path `path` that refers to an item `I` with the declared generics `decl_generics`,
/// returns an appropriate set of substitutions for this particular reference to `I`.
pub fn ast_path_substs_for_ty<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    param_mode: PathParamMode,
    decl_generics: &ty::Generics<'tcx>,
    item_segment: &ast::PathSegment)
    -> Substs<'tcx>
{
}

#[derive(PartialEq, Eq)]
pub enum PathParamMode {
    // Any path in a type context.
    Explicit,
    // The `module::Type` in `module::Type::method` in an expression.
    Optional
}

fn create_region_substs<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    decl_generics: &ty::Generics<'tcx>,
    regions_provided: Vec<ty::Region>)
    -> Substs<'tcx>
{
}

/// Given the type/region arguments provided to some path (along with
/// an implicit Self, if this is a trait reference) returns the complete
/// set of substitutions. This may involve applying defaulted type parameters.
///
/// Note that the type listing given here is *exactly* what the user provided.
///
/// The `region_substs` should be the result of `create_region_substs`
/// -- that is, a substitution with no types but the correct number of
/// regions.
fn create_substs_for_ast_path<'tcx>(
    this: &AstConv<'tcx>,
    span: Span,
    param_mode: PathParamMode,
    decl_generics: &ty::Generics<'tcx>,
    self_ty: Option<Ty<'tcx>>,
    types_provided: Vec<Ty<'tcx>>,
    region_substs: Substs<'tcx>)
    -> Substs<'tcx>
{
}

struct ConvertedBinding<'tcx> {
    item_name: ast::Name,
    ty: Ty<'tcx>,
    span: Span,
}

fn convert_angle_bracketed_parameters<'tcx>(this: &AstConv<'tcx>,
                                            rscope: &RegionScope,
                                            span: Span,
                                            decl_generics: &ty::Generics<'tcx>,
                                            data: &ast::AngleBracketedParameterData)
                                            -> (Substs<'tcx>,
                                                Vec<Ty<'tcx>>,
                                                Vec<ConvertedBinding<'tcx>>)
{
}

/// Returns the appropriate lifetime to use for any output lifetimes
/// (if one exists) and a vector of the (pattern, number of lifetimes)
/// corresponding to each input type/pattern.
fn find_implied_output_region(input_tys: &[Ty], input_pats: Vec<String>)
                              -> (Option<ty::Region>, Vec<(String, usize)>)
{
}

fn convert_ty_with_lifetime_elision<'tcx>(this: &AstConv<'tcx>,
                                          implied_output_region: Option<ty::Region>,
                                          param_lifetimes: Vec<(String, usize)>,
                                          ty: &ast::Ty)
                                          -> Ty<'tcx>
{
}

fn convert_parenthesized_parameters<'tcx>(this: &AstConv<'tcx>,
                                          rscope: &RegionScope,
                                          span: Span,
                                          decl_generics: &ty::Generics<'tcx>,
                                          data: &ast::ParenthesizedParameterData)
                                          -> (Substs<'tcx>,
                                              Vec<Ty<'tcx>>,
                                              Vec<ConvertedBinding<'tcx>>)
{
}

pub fn instantiate_poly_trait_ref<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    ast_trait_ref: &ast::PolyTraitRef,
    self_ty: Option<Ty<'tcx>>,
    poly_projections: &mut Vec<ty::PolyProjectionPredicate<'tcx>>)
    -> ty::PolyTraitRef<'tcx>
{
}

/// Instantiates the path for the given trait reference, assuming that it's
/// bound to a valid trait type. Returns the def_id for the defining trait.
/// Fails if the type is a type other than a trait type.
///
/// If the `projections` argument is `None`, then assoc type bindings like `Foo<T=X>`
/// are disallowed. Otherwise, they are pushed onto the vector given.
pub fn instantiate_mono_trait_ref<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    trait_ref: &ast::TraitRef,
    self_ty: Option<Ty<'tcx>>)
    -> ty::TraitRef<'tcx>
{
}

fn trait_def_id<'tcx>(this: &AstConv<'tcx>, trait_ref: &ast::TraitRef) -> ast::DefId {
}

fn object_path_to_poly_trait_ref<'a,'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    param_mode: PathParamMode,
    trait_def_id: ast::DefId,
    trait_segment: &ast::PathSegment,
    mut projections: &mut Vec<ty::PolyProjectionPredicate<'tcx>>)
    -> ty::PolyTraitRef<'tcx>
{
}

fn ast_path_to_poly_trait_ref<'a,'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    param_mode: PathParamMode,
    trait_def_id: ast::DefId,
    self_ty: Option<Ty<'tcx>>,
    trait_segment: &ast::PathSegment,
    poly_projections: &mut Vec<ty::PolyProjectionPredicate<'tcx>>)
    -> ty::PolyTraitRef<'tcx>
{
}

fn ast_path_to_mono_trait_ref<'a,'tcx>(this: &AstConv<'tcx>,
                                       rscope: &RegionScope,
                                       span: Span,
                                       param_mode: PathParamMode,
                                       trait_def_id: ast::DefId,
                                       self_ty: Option<Ty<'tcx>>,
                                       trait_segment: &ast::PathSegment)
                                       -> ty::TraitRef<'tcx>
{
}

fn create_substs_for_ast_trait_ref<'a,'tcx>(this: &AstConv<'tcx>,
                                            rscope: &RegionScope,
                                            span: Span,
                                            param_mode: PathParamMode,
                                            trait_def_id: ast::DefId,
                                            self_ty: Option<Ty<'tcx>>,
                                            trait_segment: &ast::PathSegment)
                                            -> (&'tcx Substs<'tcx>, Vec<ConvertedBinding<'tcx>>)
{
}

fn ast_type_binding_to_poly_projection_predicate<'tcx>(
    this: &AstConv<'tcx>,
    mut trait_ref: ty::PolyTraitRef<'tcx>,
    self_ty: Option<Ty<'tcx>>,
    binding: &ConvertedBinding<'tcx>)
    -> Result<ty::PolyProjectionPredicate<'tcx>, ErrorReported>
{
}

fn ast_path_to_ty<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    param_mode: PathParamMode,
    did: ast::DefId,
    item_segment: &ast::PathSegment)
    -> Ty<'tcx>
{
}

type TraitAndProjections<'tcx> = (ty::PolyTraitRef<'tcx>, Vec<ty::PolyProjectionPredicate<'tcx>>);

fn ast_ty_to_trait_ref<'tcx>(this: &AstConv<'tcx>,
                             rscope: &RegionScope,
                             ty: &ast::Ty,
                             bounds: &[ast::TyParamBound])
                             -> Result<TraitAndProjections<'tcx>, ErrorReported>
{
}

fn trait_ref_to_object_type<'tcx>(this: &AstConv<'tcx>,
                                  rscope: &RegionScope,
                                  span: Span,
                                  trait_ref: ty::PolyTraitRef<'tcx>,
                                  projection_bounds: Vec<ty::PolyProjectionPredicate<'tcx>>,
                                  bounds: &[ast::TyParamBound])
                                  -> Ty<'tcx>
{
}

fn make_object_type<'tcx>(this: &AstConv<'tcx>,
                          span: Span,
                          principal: ty::PolyTraitRef<'tcx>,
                          bounds: ty::ExistentialBounds<'tcx>)
                          -> Ty<'tcx> {
}

fn report_ambiguous_associated_type(tcx: &ty::ctxt,
                                    span: Span,
                                    type_str: &str,
                                    trait_str: &str,
                                    name: &str) {
}

// Search for a bound on a type parameter which includes the associated item
// given by assoc_name. ty_param_node_id is the node id for the type parameter
// (which might be `Self`, but only if it is the `Self` of a trait, not an
// impl). This function will fail if there are no suitable bounds or there is
// any ambiguity.
fn find_bound_for_assoc_item<'tcx>(this: &AstConv<'tcx>,
                                   ty_param_node_id: ast::NodeId,
                                   assoc_name: ast::Name,
                                   span: Span)
                                   -> Result<ty::PolyTraitRef<'tcx>, ErrorReported>
{
}


// Checks that bounds contains exactly one element and reports appropriate
// errors otherwise.
fn one_bound_for_assoc_type<'tcx>(tcx: &ty::ctxt<'tcx>,
                                  bounds: Vec<ty::PolyTraitRef<'tcx>>,
                                  ty_param_name: &str,
                                  assoc_name: &str,
                                  span: Span)
    -> Result<ty::PolyTraitRef<'tcx>, ErrorReported>
{
}

// Create a type from a a path to an associated type.
// For a path A::B::C::D, ty and ty_path_def are the type and def for A::B::C
// and item_segment is the path segment for D. We return a type and a def for
// the whole path.
// Will fail except for T::A and Self::A; i.e., if ty/ty_path_def are not a type
// parameter or Self.
fn associated_path_def_to_ty<'tcx>(this: &AstConv<'tcx>,
                                   span: Span,
                                   ty: Ty<'tcx>,
                                   ty_path_def: def::Def,
                                   item_segment: &ast::PathSegment)
                                   -> (Ty<'tcx>, def::Def)
{
}

fn qpath_to_ty<'tcx>(this: &AstConv<'tcx>,
                     rscope: &RegionScope,
                     span: Span,
                     param_mode: PathParamMode,
                     opt_self_ty: Option<Ty<'tcx>>,
                     trait_def_id: ast::DefId,
                     trait_segment: &ast::PathSegment,
                     item_segment: &ast::PathSegment)
                     -> Ty<'tcx>
{
}

/// Convert a type supplied as value for a type argument from AST into our
/// our internal representation. This is the same as `ast_ty_to_ty` but that
/// it applies the object lifetime default.
///
/// # Parameters
///
/// * `this`, `rscope`: the surrounding context
/// * `decl_generics`: the generics of the struct/enum/trait declaration being
///   referenced
/// * `index`: the index of the type parameter being instantiated from the list
///   (we assume it is in the `TypeSpace`)
/// * `region_substs`: a partial substitution consisting of
///   only the region type parameters being supplied to this type.
/// * `ast_ty`: the ast representation of the type being supplied
pub fn ast_ty_arg_to_ty<'tcx>(this: &AstConv<'tcx>,
                              rscope: &RegionScope,
                              decl_generics: &ty::Generics<'tcx>,
                              index: usize,
                              region_substs: &Substs<'tcx>,
                              ast_ty: &ast::Ty)
                              -> Ty<'tcx>
{
}

// Check the base def in a PathResolution and convert it to a Ty. If there are
// associated types in the PathResolution, these will need to be separately
// resolved.
fn base_def_to_ty<'tcx>(this: &AstConv<'tcx>,
                        rscope: &RegionScope,
                        span: Span,
                        param_mode: PathParamMode,
                        def: &def::Def,
                        opt_self_ty: Option<Ty<'tcx>>,
                        base_segments: &[ast::PathSegment])
                        -> Ty<'tcx> {
}

// Note that both base_segments and assoc_segments may be empty, although not at
// the same time.
pub fn finish_resolving_def_to_ty<'tcx>(this: &AstConv<'tcx>,
                                        rscope: &RegionScope,
                                        span: Span,
                                        param_mode: PathParamMode,
                                        def: &def::Def,
                                        opt_self_ty: Option<Ty<'tcx>>,
                                        base_segments: &[ast::PathSegment],
                                        assoc_segments: &[ast::PathSegment])
                                        -> Ty<'tcx> {
}

/// Parses the programmer's textual representation of a type into our
/// internal notion of a type.
pub fn ast_ty_to_ty<'tcx>(this: &AstConv<'tcx>,
                          rscope: &RegionScope,
                          ast_ty: &ast::Ty)
                          -> Ty<'tcx>
{
}

pub fn ty_of_arg<'tcx>(this: &AstConv<'tcx>,
                       rscope: &RegionScope,
                       a: &ast::Arg,
                       expected_ty: Option<Ty<'tcx>>)
                       -> Ty<'tcx>
{
}

struct SelfInfo<'a, 'tcx> {
    untransformed_self_ty: Ty<'tcx>,
    explicit_self: &'a ast::ExplicitSelf,
}

pub fn ty_of_method<'tcx>(this: &AstConv<'tcx>,
                          sig: &ast::MethodSig,
                          untransformed_self_ty: Ty<'tcx>)
                          -> (ty::BareFnTy<'tcx>, ty::ExplicitSelfCategory) {
}

pub fn ty_of_bare_fn<'tcx>(this: &AstConv<'tcx>, unsafety: ast::Unsafety, abi: abi::Abi,
                                              decl: &ast::FnDecl) -> ty::BareFnTy<'tcx> {
}

fn ty_of_method_or_bare_fn<'a, 'tcx>(this: &AstConv<'tcx>,
                                     unsafety: ast::Unsafety,
                                     abi: abi::Abi,
                                     opt_self_info: Option<SelfInfo<'a, 'tcx>>,
                                     decl: &ast::FnDecl)
                                     -> (ty::BareFnTy<'tcx>, Option<ty::ExplicitSelfCategory>)
{
}

fn determine_explicit_self_category<'a, 'tcx>(this: &AstConv<'tcx>,
                                              rscope: &RegionScope,
                                              self_info: &SelfInfo<'a, 'tcx>)
                                              -> ty::ExplicitSelfCategory
{
}

pub fn ty_of_closure<'tcx>(
    this: &AstConv<'tcx>,
    unsafety: ast::Unsafety,
    decl: &ast::FnDecl,
    abi: abi::Abi,
    expected_sig: Option<ty::FnSig<'tcx>>)
    -> ty::ClosureTy<'tcx>
{
}

/// Given an existential type like `Foo+'a+Bar`, this routine converts the `'a` and `Bar` intos an
/// `ExistentialBounds` struct. The `main_trait_refs` argument specifies the `Foo` -- it is absent
/// for closures. Eventually this should all be normalized, I think, so that there is no "main
/// trait ref" and instead we just have a flat list of bounds as the existential type.
fn conv_existential_bounds<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    principal_trait_ref: ty::PolyTraitRef<'tcx>,
    projection_bounds: Vec<ty::PolyProjectionPredicate<'tcx>>,
    ast_bounds: &[ast::TyParamBound])
    -> ty::ExistentialBounds<'tcx>
{
}

fn conv_ty_poly_trait_ref<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    ast_bounds: &[ast::TyParamBound])
    -> Ty<'tcx>
{
}

pub fn conv_existential_bounds_from_partitioned_bounds<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    principal_trait_ref: ty::PolyTraitRef<'tcx>,
    mut projection_bounds: Vec<ty::PolyProjectionPredicate<'tcx>>, // Empty for boxed closures
    partitioned_bounds: PartitionedBounds)
    -> ty::ExistentialBounds<'tcx>
{
}

/// Given the bounds on an object, determines what single region bound
/// (if any) we can use to summarize this type. The basic idea is that we will use the bound the
/// user provided, if they provided one, and otherwise search the supertypes of trait bounds for
/// region bounds. It may be that we can derive no bound at all, in which case we return `None`.
fn compute_object_lifetime_bound<'tcx>(
    this: &AstConv<'tcx>,
    rscope: &RegionScope,
    span: Span,
    explicit_region_bounds: &[&ast::Lifetime],
    principal_trait_ref: ty::PolyTraitRef<'tcx>,
    builtin_bounds: ty::BuiltinBounds)
    -> ty::Region
{
}

pub struct PartitionedBounds<'a> {
    pub builtin_bounds: ty::BuiltinBounds,
    pub trait_bounds: Vec<&'a ast::PolyTraitRef>,
    pub region_bounds: Vec<&'a ast::Lifetime>,
}

/// Divides a list of bounds from the AST into three groups: builtin bounds (Copy, Sized etc),
/// general trait bounds, and region bounds.
pub fn partition_bounds<'a>(tcx: &ty::ctxt,
                            _span: Span,
                            ast_bounds: &'a [ast::TyParamBound])
                            -> PartitionedBounds<'a>
{
}

fn prohibit_projections<'tcx>(tcx: &ty::ctxt<'tcx>,
                              bindings: &[ConvertedBinding<'tcx>])
{
}

fn check_type_argument_count(tcx: &ty::ctxt, span: Span, supplied: usize,
                             required: usize, accepted: usize) {
}

fn report_lifetime_number_error(tcx: &ty::ctxt, span: Span, number: usize, expected: usize) {
}

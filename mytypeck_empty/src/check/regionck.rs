// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The region check is a final pass that runs over the AST after we have
//! inferred the type constraints but before we have actually finalized
//! the types.  Its purpose is to embed a variety of region constraints.
//! Inserting these constraints as a separate pass is good because (1) it
//! localizes the code that has to do with region inference and (2) often
//! we cannot know what constraints are needed until the basic types have
//! been inferred.
//!
//! ### Interaction with the borrow checker
//!
//! In general, the job of the borrowck module (which runs later) is to
//! check that all soundness criteria are met, given a particular set of
//! regions. The job of *this* module is to anticipate the needs of the
//! borrow checker and infer regions that will satisfy its requirements.
//! It is generally true that the inference doesn't need to be sound,
//! meaning that if there is a bug and we inferred bad regions, the borrow
//! checker should catch it. This is not entirely true though; for
//! example, the borrow checker doesn't check subtyping, and it doesn't
//! check that region pointers are always live when they are used. It
//! might be worthwhile to fix this so that borrowck serves as a kind of
//! verification step -- that would add confidence in the overall
//! correctness of the compiler, at the cost of duplicating some type
//! checks and effort.
//!
//! ### Inferring the duration of borrows, automatic and otherwise
//!
//! Whenever we introduce a borrowed pointer, for example as the result of
//! a borrow expression `let x = &data`, the lifetime of the pointer `x`
//! is always specified as a region inference variable. `regionck` has the
//! job of adding constraints such that this inference variable is as
//! narrow as possible while still accommodating all uses (that is, every
//! dereference of the resulting pointer must be within the lifetime).
//!
//! #### Reborrows
//!
//! Generally speaking, `regionck` does NOT try to ensure that the data
//! `data` will outlive the pointer `x`. That is the job of borrowck.  The
//! one exception is when "re-borrowing" the contents of another borrowed
//! pointer. For example, imagine you have a borrowed pointer `b` with
//! lifetime L1 and you have an expression `&*b`. The result of this
//! expression will be another borrowed pointer with lifetime L2 (which is
//! an inference variable). The borrow checker is going to enforce the
//! constraint that L2 < L1, because otherwise you are re-borrowing data
//! for a lifetime larger than the original loan.  However, without the
//! routines in this module, the region inferencer would not know of this
//! dependency and thus it might infer the lifetime of L2 to be greater
//! than L1 (issue #3148).
//!
//! There are a number of troublesome scenarios in the tests
//! `region-dependent-*.rs`, but here is one example:
//!
//!     struct Foo { i: int }
//!     struct Bar { foo: Foo  }
//!     fn get_i(x: &'a Bar) -> &'a int {
//!        let foo = &x.foo; // Lifetime L1
//!        &foo.i            // Lifetime L2
//!     }
//!
//! Note that this comes up either with `&` expressions, `ref`
//! bindings, and `autorefs`, which are the three ways to introduce
//! a borrow.
//!
//! The key point here is that when you are borrowing a value that
//! is "guaranteed" by a borrowed pointer, you must link the
//! lifetime of that borrowed pointer (L1, here) to the lifetime of
//! the borrow itself (L2).  What do I mean by "guaranteed" by a
//! borrowed pointer? I mean any data that is reached by first
//! dereferencing a borrowed pointer and then either traversing
//! interior offsets or owned pointers.  We say that the guarantor
//! of such data it the region of the borrowed pointer that was
//! traversed.  This is essentially the same as the ownership
//! relation, except that a borrowed pointer never owns its
//! contents.

use astconv::AstConv;
use check::dropck;
use check::FnCtxt;
use middle::free_region::FreeRegionMap;
use middle::implicator;
use middle::mem_categorization as mc;
use middle::region::CodeExtent;
use middle::subst::Substs;
use middle::traits;
use middle::ty::{self, ClosureTyper, ReScope, Ty, MethodCall};
use middle::infer::{self, GenericKind};
use middle::pat_util;
use util::ppaux::{ty_to_string, Repr};

use std::mem;
use syntax::{ast, ast_util};
use syntax::codemap::Span;
use syntax::visit;
use syntax::visit::Visitor;

use self::SubjectNode::Subject;

// a variation on try that just returns unit
macro_rules! ignore_err {
    ($e:expr) => (match $e { Ok(e) => e, Err(_) => return () })
}

///////////////////////////////////////////////////////////////////////////
// PUBLIC ENTRY POINTS

pub fn regionck_expr(fcx: &FnCtxt, e: &ast::Expr) {
}

pub fn regionck_item(fcx: &FnCtxt, item: &ast::Item) {
}

pub fn regionck_fn(fcx: &FnCtxt,
                   fn_id: ast::NodeId,
                   fn_span: Span,
                   decl: &ast::FnDecl,
                   blk: &ast::Block) {
}

/// Checks that the types in `component_tys` are well-formed. This will add constraints into the
/// region graph. Does *not* run `resolve_regions_and_report_errors` and so forth.
pub fn regionck_ensure_component_tys_wf<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                                  span: Span,
                                                  component_tys: &[Ty<'tcx>]) {
}

///////////////////////////////////////////////////////////////////////////
// INTERNALS

pub struct Rcx<'a, 'tcx: 'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,

    region_bound_pairs: Vec<(ty::Region, GenericKind<'tcx>)>,

    free_region_map: FreeRegionMap,

    // id of innermost fn body id
    body_id: ast::NodeId,

    // id of innermost fn or loop
    repeating_scope: ast::NodeId,

    // id of AST node being analyzed (the subject of the analysis).
    subject: SubjectNode,

}

pub struct RepeatingScope(ast::NodeId);
pub enum SubjectNode { Subject(ast::NodeId), None }

impl<'a, 'tcx> Rcx<'a, 'tcx> {
    pub fn new(fcx: &'a FnCtxt<'a, 'tcx>,
               initial_repeating_scope: RepeatingScope,
               initial_body_id: ast::NodeId,
               subject: SubjectNode) -> Rcx<'a, 'tcx> {
    }

    pub fn tcx(&self) -> &'a ty::ctxt<'tcx> {
    }

    fn set_body_id(&mut self, body_id: ast::NodeId) -> ast::NodeId {
    }

    fn set_repeating_scope(&mut self, scope: ast::NodeId) -> ast::NodeId {
    }

    /// Try to resolve the type for the given node, returning t_err if an error results.  Note that
    /// we never care about the details of the error, the same error will be detected and reported
    /// in the writeback phase.
    ///
    /// Note one important point: we do not attempt to resolve *region variables* here.  This is
    /// because regionck is essentially adding constraints to those region variables and so may yet
    /// influence how they are resolved.
    ///
    /// Consider this silly example:
    ///
    /// ```
    /// fn borrow(x: &int) -> &int {x}
    /// fn foo(x: @int) -> int {  // block: B
    ///     let b = borrow(x);    // region: <R0>
    ///     *b
    /// }
    /// ```
    ///
    /// Here, the region of `b` will be `<R0>`.  `<R0>` is constrained to be some subregion of the
    /// block B and some superregion of the call.  If we forced it now, we'd choose the smaller
    /// region (the call).  But that would make the *b illegal.  Since we don't resolve, the type
    /// of b will be `&<R0>.int` and then `*b` will require that `<R0>` be bigger than the let and
    /// the `*b` expression, so we will effectively resolve `<R0>` to be the block B.
    pub fn resolve_type(&self, unresolved_ty: Ty<'tcx>) -> Ty<'tcx> {
    }

    /// Try to resolve the type for the given node.
    fn resolve_node_type(&self, id: ast::NodeId) -> Ty<'tcx> {
    }

    fn resolve_method_type(&self, method_call: MethodCall) -> Option<Ty<'tcx>> {
    }

    /// Try to resolve the type for the given node.
    pub fn resolve_expr_type_adjusted(&mut self, expr: &ast::Expr) -> Ty<'tcx> {
    }

    fn visit_fn_body(&mut self,
                     id: ast::NodeId,
                     fn_decl: &ast::FnDecl,
                     body: &ast::Block,
                     span: Span)
    {
    }

    fn visit_region_obligations(&mut self, node_id: ast::NodeId)
    {
    }

    /// This method populates the region map's `free_region_map`. It walks over the transformed
    /// argument and return types for each function just before we check the body of that function,
    /// looking for types where you have a borrowed pointer to other borrowed data (e.g., `&'a &'b
    /// [usize]`.  We do not allow references to outlive the things they point at, so we can assume
    /// that `'a <= 'b`. This holds for both the argument and return types, basically because, on
    /// the caller side, the caller is responsible for checking that the type of every expression
    /// (including the actual values for the arguments, as well as the return type of the fn call)
    /// is well-formed.
    ///
    /// Tests: `src/test/compile-fail/regions-free-region-ordering-*.rs`
    fn relate_free_regions(&mut self,
                           fn_sig_tys: &[Ty<'tcx>],
                           body_id: ast::NodeId,
                           span: Span) {
    }

    fn resolve_regions_and_report_errors(&self) {
    }
}

impl<'a, 'tcx, 'v> Visitor<'v> for Rcx<'a, 'tcx> {
    // (..) FIXME(#3238) should use visit_pat, not visit_arm/visit_local,
    // However, right now we run into an issue whereby some free
    // regions are not properly related if they appear within the
    // types of arguments that must be inferred. This could be
    // addressed by deferring the construction of the region
    // hierarchy, and in particular the relationships between free
    // regions, until regionck, as described in #3238.

    fn visit_fn(&mut self, _fk: visit::FnKind<'v>, fd: &'v ast::FnDecl,
                b: &'v ast::Block, span: Span, id: ast::NodeId) {
    }

    fn visit_item(&mut self, i: &ast::Item) {}

    fn visit_expr(&mut self, ex: &ast::Expr) {}

    //visit_pat: visit_pat, // (..) see above

    fn visit_arm(&mut self, a: &ast::Arm) {}

    fn visit_local(&mut self, l: &ast::Local) {}

    fn visit_block(&mut self, b: &ast::Block) {}
}

fn visit_item(_rcx: &mut Rcx, _item: &ast::Item) {
    // Ignore items
}

fn visit_block(rcx: &mut Rcx, b: &ast::Block) {
}

fn visit_arm(rcx: &mut Rcx, arm: &ast::Arm) {
}

fn visit_local(rcx: &mut Rcx, l: &ast::Local) {
}

fn constrain_bindings_in_pat(pat: &ast::Pat, rcx: &mut Rcx) {
}

fn visit_expr(rcx: &mut Rcx, expr: &ast::Expr) {
}

fn constrain_cast(rcx: &mut Rcx,
                  cast_expr: &ast::Expr,
                  source_expr: &ast::Expr)
{
}

fn check_expr_fn_block(rcx: &mut Rcx,
                       expr: &ast::Expr,
                       body: &ast::Block) {
}

fn constrain_callee(rcx: &mut Rcx,
                    callee_id: ast::NodeId,
                    _call_expr: &ast::Expr,
                    _callee_expr: &ast::Expr) {
}

fn constrain_call<'a, I: Iterator<Item=&'a ast::Expr>>(rcx: &mut Rcx,
                                                       call_expr: &ast::Expr,
                                                       receiver: Option<&ast::Expr>,
                                                       arg_exprs: I,
                                                       implicitly_ref_args: bool) {
}

/// Invoked on any auto-dereference that occurs. Checks that if this is a region pointer being
/// dereferenced, the lifetime of the pointer includes the deref expr.
fn constrain_autoderefs<'a, 'tcx>(rcx: &mut Rcx<'a, 'tcx>,
                                  deref_expr: &ast::Expr,
                                  derefs: usize,
                                  mut derefd_ty: Ty<'tcx>)
{
}

pub fn mk_subregion_due_to_dereference(rcx: &mut Rcx,
                                       deref_span: Span,
                                       minimum_lifetime: ty::Region,
                                       maximum_lifetime: ty::Region) {
}

fn check_safety_of_rvalue_destructor_if_necessary<'a, 'tcx>(rcx: &mut Rcx<'a, 'tcx>,
                                                            cmt: mc::cmt<'tcx>,
                                                            span: Span) {
}

/// Invoked on any index expression that occurs. Checks that if this is a slice being indexed, the
/// lifetime of the pointer includes the deref expr.
fn constrain_index<'a, 'tcx>(rcx: &mut Rcx<'a, 'tcx>,
                             index_expr: &ast::Expr,
                             indexed_ty: Ty<'tcx>)
{
}

/// Guarantees that any lifetimes which appear in the type of the node `id` (after applying
/// adjustments) are valid for at least `minimum_lifetime`
fn type_of_node_must_outlive<'a, 'tcx>(
    rcx: &mut Rcx<'a, 'tcx>,
    origin: infer::SubregionOrigin<'tcx>,
    id: ast::NodeId,
    minimum_lifetime: ty::Region)
{
}

/// Computes the guarantors for any ref bindings in a `let` and
/// then ensures that the lifetime of the resulting pointer is
/// linked to the lifetime of the initialization expression.
fn link_local(rcx: &Rcx, local: &ast::Local) {
}

/// Computes the guarantors for any ref bindings in a match and
/// then ensures that the lifetime of the resulting pointer is
/// linked to the lifetime of its guarantor (if any).
fn link_match(rcx: &Rcx, discr: &ast::Expr, arms: &[ast::Arm]) {
}

/// Computes the guarantors for any ref bindings in a match and
/// then ensures that the lifetime of the resulting pointer is
/// linked to the lifetime of its guarantor (if any).
fn link_fn_args(rcx: &Rcx, body_scope: CodeExtent, args: &[ast::Arg]) {
}

/// Link lifetimes of any ref bindings in `root_pat` to the pointers found in the discriminant, if
/// needed.
fn link_pattern<'a, 'tcx>(rcx: &Rcx<'a, 'tcx>,
                          mc: mc::MemCategorizationContext<FnCtxt<'a, 'tcx>>,
                          discr_cmt: mc::cmt<'tcx>,
                          root_pat: &ast::Pat) {
}

/// Link lifetime of borrowed pointer resulting from autoref to lifetimes in the value being
/// autoref'd.
fn link_autoref(rcx: &Rcx,
                expr: &ast::Expr,
                autoderefs: usize,
                autoref: &ty::AutoRef)
{
}

/// Computes the guarantor for cases where the `expr` is being passed by implicit reference and
/// must outlive `callee_scope`.
fn link_by_ref(rcx: &Rcx,
               expr: &ast::Expr,
               callee_scope: CodeExtent) {

}

/// Like `link_region()`, except that the region is extracted from the type of `id`, which must be
/// some reference (`&T`, `&str`, etc).
fn link_region_from_node_type<'a, 'tcx>(rcx: &Rcx<'a, 'tcx>,
                                        span: Span,
                                        id: ast::NodeId,
                                        mutbl: ast::Mutability,
                                        cmt_borrowed: mc::cmt<'tcx>) {
}

/// Informs the inference engine that `borrow_cmt` is being borrowed with kind `borrow_kind` and
/// lifetime `borrow_region`. In order to ensure borrowck is satisfied, this may create constraints
/// between regions, as explained in `link_reborrowed_region()`.
fn link_region<'a, 'tcx>(rcx: &Rcx<'a, 'tcx>,
                         span: Span,
                         borrow_region: &ty::Region,
                         borrow_kind: ty::BorrowKind,
                         borrow_cmt: mc::cmt<'tcx>) {
}

/// This is the most complicated case: the path being borrowed is
/// itself the referent of a borrowed pointer. Let me give an
/// example fragment of code to make clear(er) the situation:
///
///    let r: &'a mut T = ...;  // the original reference "r" has lifetime 'a
///    ...
///    &'z *r                   // the reborrow has lifetime 'z
///
/// Now, in this case, our primary job is to add the inference
/// constraint that `'z <= 'a`. Given this setup, let's clarify the
/// parameters in (roughly) terms of the example:
///
///     A borrow of: `& 'z bk * r` where `r` has type `& 'a bk T`
///     borrow_region   ^~                 ref_region    ^~
///     borrow_kind        ^~               ref_kind        ^~
///     ref_cmt                 ^
///
/// Here `bk` stands for some borrow-kind (e.g., `mut`, `uniq`, etc).
///
/// Unfortunately, there are some complications beyond the simple
/// scenario I just painted:
///
/// 1. The reference `r` might in fact be a "by-ref" upvar. In that
///    case, we have two jobs. First, we are inferring whether this reference
///    should be an `&T`, `&mut T`, or `&uniq T` reference, and we must
///    adjust that based on this borrow (e.g., if this is an `&mut` borrow,
///    then `r` must be an `&mut` reference). Second, whenever we link
///    two regions (here, `'z <= 'a`), we supply a *cause*, and in this
///    case we adjust the cause to indicate that the reference being
///    "reborrowed" is itself an upvar. This provides a nicer error message
///    should something go wrong.
///
/// 2. There may in fact be more levels of reborrowing. In the
///    example, I said the borrow was like `&'z *r`, but it might
///    in fact be a borrow like `&'z **q` where `q` has type `&'a
///    &'b mut T`. In that case, we want to ensure that `'z <= 'a`
///    and `'z <= 'b`. This is explained more below.
///
/// The return value of this function indicates whether we need to
/// recurse and process `ref_cmt` (see case 2 above).
fn link_reborrowed_region<'a, 'tcx>(rcx: &Rcx<'a, 'tcx>,
                                    span: Span,
                                    borrow_region: &ty::Region,
                                    borrow_kind: ty::BorrowKind,
                                    ref_cmt: mc::cmt<'tcx>,
                                    ref_region: ty::Region,
                                    mut ref_kind: ty::BorrowKind,
                                    note: mc::Note)
                                    -> Option<(mc::cmt<'tcx>, ty::BorrowKind)>
{
}

/// Ensures that all borrowed data reachable via `ty` outlives `region`.
pub fn type_must_outlive<'a, 'tcx>(rcx: &mut Rcx<'a, 'tcx>,
                               origin: infer::SubregionOrigin<'tcx>,
                               ty: Ty<'tcx>,
                               region: ty::Region)
{
}

fn closure_must_outlive<'a, 'tcx>(rcx: &mut Rcx<'a, 'tcx>,
                                  origin: infer::SubregionOrigin<'tcx>,
                                  region: ty::Region,
                                  def_id: ast::DefId,
                                  substs: &'tcx Substs<'tcx>) {
}

fn generic_must_outlive<'a, 'tcx>(rcx: &Rcx<'a, 'tcx>,
                                  origin: infer::SubregionOrigin<'tcx>,
                                  region: ty::Region,
                                  generic: &GenericKind<'tcx>) {
}

fn projection_bounds<'a,'tcx>(rcx: &Rcx<'a, 'tcx>,
                              span: Span,
                              projection_ty: &ty::ProjectionTy<'tcx>)
                              -> Vec<ty::Region>
{
}

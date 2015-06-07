// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::MethodError;
use super::ItemIndex;
use super::{CandidateSource,ImplSource,TraitSource};
use super::suggest;

use check;
use check::{FnCtxt, NoPreference, UnresolvedTypeAction};
use middle::fast_reject;
use middle::subst;
use middle::subst::Subst;
use middle::traits;
use middle::ty::{self, RegionEscape, Ty, ToPolyTraitRef};
use middle::ty_fold::TypeFoldable;
use middle::infer;
use middle::infer::InferCtxt;
use syntax::ast;
use syntax::codemap::{Span, DUMMY_SP};
use std::collections::HashSet;
use std::mem;
use std::rc::Rc;
use util::ppaux::Repr;

use self::CandidateKind::*;
pub use self::PickKind::*;

struct ProbeContext<'a, 'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    mode: Mode,
    item_name: ast::Name,
    steps: Rc<Vec<CandidateStep<'tcx>>>,
    opt_simplified_steps: Option<Vec<fast_reject::SimplifiedType>>,
    inherent_candidates: Vec<Candidate<'tcx>>,
    extension_candidates: Vec<Candidate<'tcx>>,
    impl_dups: HashSet<ast::DefId>,
    static_candidates: Vec<CandidateSource>,
}

struct CandidateStep<'tcx> {
    self_ty: Ty<'tcx>,
    autoderefs: usize,
    unsize: bool
}

struct Candidate<'tcx> {
    xform_self_ty: Ty<'tcx>,
    item: ty::ImplOrTraitItem<'tcx>,
    kind: CandidateKind<'tcx>,
}

enum CandidateKind<'tcx> {
    InherentImplCandidate(/* Impl */ ast::DefId, subst::Substs<'tcx>),
    ObjectCandidate(/* Trait */ ast::DefId, /* method_num */ usize, /* vtable index */ usize),
    ExtensionImplCandidate(/* Impl */ ast::DefId, ty::TraitRef<'tcx>,
                           subst::Substs<'tcx>, ItemIndex),
    ClosureCandidate(/* Trait */ ast::DefId, ItemIndex),
    WhereClauseCandidate(ty::PolyTraitRef<'tcx>, ItemIndex),
    ProjectionCandidate(ast::DefId, ItemIndex),
}

pub struct Pick<'tcx> {
    pub item: ty::ImplOrTraitItem<'tcx>,
    pub kind: PickKind<'tcx>,

    // Indicates that the source expression should be autoderef'd N times
    //
    // A = expr | *expr | **expr | ...
    pub autoderefs: usize,

    // Indicates that an autoref is applied after the optional autoderefs
    //
    // B = A | &A | &mut A
    pub autoref: Option<ast::Mutability>,

    // Indicates that the source expression should be "unsized" to a
    // target type. This should probably eventually go away in favor
    // of just coercing method receivers.
    //
    // C = B | unsize(B)
    pub unsize: Option<Ty<'tcx>>,
}

#[derive(Clone,Debug)]
pub enum PickKind<'tcx> {
    InherentImplPick(/* Impl */ ast::DefId),
    ObjectPick(/* Trait */ ast::DefId, /* method_num */ usize, /* real_index */ usize),
    ExtensionImplPick(/* Impl */ ast::DefId, ItemIndex),
    TraitPick(/* Trait */ ast::DefId, ItemIndex),
    WhereClausePick(/* Trait */ ty::PolyTraitRef<'tcx>, ItemIndex),
}

pub type PickResult<'tcx> = Result<Pick<'tcx>, MethodError>;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Mode {
    // An expression of the form `receiver.method_name(...)`.
    // Autoderefs are performed on `receiver`, lookup is done based on the
    // `self` argument  of the method, and static methods aren't considered.
    MethodCall,
    // An expression of the form `Type::item` or `<T>::item`.
    // No autoderefs are performed, lookup is done based on the type each
    // implementation is for, and static methods are included.
    Path
}

pub fn probe<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                       span: Span,
                       mode: Mode,
                       item_name: ast::Name,
                       self_ty: Ty<'tcx>,
                       scope_expr_id: ast::NodeId)
                       -> PickResult<'tcx>
{
}

impl<'a,'tcx> ProbeContext<'a,'tcx> {
    fn new(fcx: &'a FnCtxt<'a,'tcx>,
           span: Span,
           mode: Mode,
           item_name: ast::Name,
           steps: Vec<CandidateStep<'tcx>>,
           opt_simplified_steps: Option<Vec<fast_reject::SimplifiedType>>)
           -> ProbeContext<'a,'tcx>
    {
    }

    fn reset(&mut self) {
    }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
    }

    fn infcx(&self) -> &'a InferCtxt<'a, 'tcx> {
    }

    ///////////////////////////////////////////////////////////////////////////
    // CANDIDATE ASSEMBLY

    fn assemble_inherent_candidates(&mut self) {
    }

    fn assemble_probe(&mut self, self_ty: Ty<'tcx>) {
    }

    fn assemble_inherent_impl_for_primitive(&mut self, lang_def_id: Option<ast::DefId>) {
    }

    fn assemble_inherent_impl_candidates_for_type(&mut self, def_id: ast::DefId) {
    }

    fn assemble_inherent_impl_probe(&mut self, impl_def_id: ast::DefId) {
    }

    fn assemble_inherent_candidates_from_object(&mut self,
                                                self_ty: Ty<'tcx>,
                                                data: &ty::TyTrait<'tcx>) {
    }

    fn assemble_inherent_candidates_from_param(&mut self,
                                               _rcvr_ty: Ty<'tcx>,
                                               param_ty: ty::ParamTy) {
    }

    // Do a search through a list of bounds, using a callback to actually
    // create the candidates.
    fn elaborate_bounds<F>(
        &mut self,
        bounds: &[ty::PolyTraitRef<'tcx>],
        mut mk_cand: F,
    ) where
        F: for<'b> FnMut(
            &mut ProbeContext<'b, 'tcx>,
            ty::PolyTraitRef<'tcx>,
            ty::ImplOrTraitItem<'tcx>,
            usize,
        ),
    {
    }

    fn assemble_extension_candidates_for_traits_in_scope(&mut self,
                                                         expr_id: ast::NodeId)
                                                         -> Result<(),MethodError>
    {
    }

    fn assemble_extension_candidates_for_all_traits(&mut self) -> Result<(),MethodError> {
    }

    fn assemble_extension_candidates_for_trait(&mut self,
                                               trait_def_id: ast::DefId)
                                               -> Result<(),MethodError>
    {
    }

    fn assemble_extension_candidates_for_trait_impls(&mut self,
                                                     trait_def_id: ast::DefId,
                                                     item: ty::ImplOrTraitItem<'tcx>,
                                                     item_index: usize)
    {
    }

    fn impl_can_possibly_match(&self, impl_def_id: ast::DefId) -> bool {
    }

    fn assemble_closure_candidates(&mut self,
                                   trait_def_id: ast::DefId,
                                   item: ty::ImplOrTraitItem<'tcx>,
                                   item_index: usize)
                                   -> Result<(),MethodError>
    {
    }

    fn assemble_projection_candidates(&mut self,
                                      trait_def_id: ast::DefId,
                                      item: ty::ImplOrTraitItem<'tcx>,
                                      item_index: usize)
    {
    }

    fn assemble_where_clause_candidates(&mut self,
                                        trait_def_id: ast::DefId,
                                        item: ty::ImplOrTraitItem<'tcx>,
                                        item_index: usize)
    {
    }

    ///////////////////////////////////////////////////////////////////////////
    // THE ACTUAL SEARCH

    fn pick(mut self) -> PickResult<'tcx> {
    }

    fn pick_core(&mut self) -> Option<PickResult<'tcx>> {
    }

    fn pick_step(&mut self, step: &CandidateStep<'tcx>) -> Option<PickResult<'tcx>> {
    }

    fn pick_by_value_method(&mut self,
                            step: &CandidateStep<'tcx>)
                            -> Option<PickResult<'tcx>>
    {
    }

    fn pick_autorefd_method(&mut self,
                            step: &CandidateStep<'tcx>)
                            -> Option<PickResult<'tcx>>
    {
    }

    fn pick_method(&mut self, self_ty: Ty<'tcx>) -> Option<PickResult<'tcx>> {
    }

    fn consider_candidates(&self,
                           self_ty: Ty<'tcx>,
                           probes: &[Candidate<'tcx>])
                           -> Option<PickResult<'tcx>> {
    }

    fn consider_probe(&self, self_ty: Ty<'tcx>, probe: &Candidate<'tcx>) -> bool {
    }

    /// Sometimes we get in a situation where we have multiple probes that are all impls of the
    /// same trait, but we don't know which impl to use. In this case, since in all cases the
    /// external interface of the method can be determined from the trait, it's ok not to decide.
    /// We can basically just collapse all of the probes for various impls into one where-clause
    /// probe. This will result in a pending obligation so when more type-info is available we can
    /// make the final decision.
    ///
    /// Example (`src/test/run-pass/method-two-trait-defer-resolution-1.rs`):
    ///
    /// ```
    /// trait Foo { ... }
    /// impl Foo for Vec<int> { ... }
    /// impl Foo for Vec<usize> { ... }
    /// ```
    ///
    /// Now imagine the receiver is `Vec<_>`. It doesn't really matter at this time which impl we
    /// use, so it's ok to just commit to "using the method from the trait Foo".
    fn collapse_candidates_to_trait_pick(&self,
                                         probes: &[&Candidate<'tcx>])
                                         -> Option<Pick<'tcx>> {
    }

    ///////////////////////////////////////////////////////////////////////////
    // MISCELLANY

    fn make_sub_ty(&self, sub: Ty<'tcx>, sup: Ty<'tcx>) -> infer::UnitResult<'tcx> {
    }

    fn has_applicable_self(&self, item: &ty::ImplOrTraitItem) -> bool {
    }

    fn record_static_candidate(&mut self, source: CandidateSource) {
    }

    fn xform_self_ty(&self,
                     item: &ty::ImplOrTraitItem<'tcx>,
                     impl_ty: Ty<'tcx>,
                     substs: &subst::Substs<'tcx>)
                     -> Ty<'tcx>
    {
    }

    fn xform_method_self_ty(&self,
                            method: &Rc<ty::Method<'tcx>>,
                            impl_ty: Ty<'tcx>,
                            substs: &subst::Substs<'tcx>)
                            -> Ty<'tcx>
    {
    }

    /// Get the type of an impl and generate substitutions with placeholders.
    fn impl_ty_and_substs(&self,
                          impl_def_id: ast::DefId)
                          -> (Ty<'tcx>, subst::Substs<'tcx>)
    {
    }

    /// Replace late-bound-regions bound by `value` with `'static` using
    /// `ty::erase_late_bound_regions`.
    ///
    /// This is only a reasonable thing to do during the *probe* phase, not the *confirm* phase, of
    /// method matching. It is reasonable during the probe phase because we don't consider region
    /// relationships at all. Therefore, we can just replace all the region variables with 'static
    /// rather than creating fresh region variables. This is nice for two reasons:
    ///
    /// 1. Because the numbers of the region variables would otherwise be fairly unique to this
    ///    particular method call, it winds up creating fewer types overall, which helps for memory
    ///    usage. (Admittedly, this is a rather small effect, though measureable.)
    ///
    /// 2. It makes it easier to deal with higher-ranked trait bounds, because we can replace any
    ///    late-bound regions with 'static. Otherwise, if we were going to replace late-bound
    ///    regions with actual region variables as is proper, we'd have to ensure that the same
    ///    region got replaced with the same variable, which requires a bit more coordination
    ///    and/or tracking the substitution and
    ///    so forth.
    fn erase_late_bound_regions<T>(&self, value: &ty::Binder<T>) -> T
        where T : TypeFoldable<'tcx> + Repr<'tcx>
    {
    }
}

fn impl_item<'tcx>(tcx: &ty::ctxt<'tcx>,
                   impl_def_id: ast::DefId,
                   item_name: ast::Name)
                   -> Option<ty::ImplOrTraitItem<'tcx>>
{
}

/// Find item with name `item_name` defined in `trait_def_id` and return it,
/// along with its index (or `None`, if no such item).
fn trait_item<'tcx>(tcx: &ty::ctxt<'tcx>,
                    trait_def_id: ast::DefId,
                    item_name: ast::Name)
                    -> Option<(usize, ty::ImplOrTraitItem<'tcx>)>
{
}

impl<'tcx> Candidate<'tcx> {
    fn to_unadjusted_pick(&self) -> Pick<'tcx> {
    }

    fn to_source(&self) -> CandidateSource {
    }

    fn to_trait_data(&self) -> Option<(ast::DefId, ItemIndex)> {
    }
}

impl<'tcx> Repr<'tcx> for Candidate<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
    }
}

impl<'tcx> Repr<'tcx> for CandidateKind<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
    }
}

impl<'tcx> Repr<'tcx> for CandidateStep<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
    }
}

impl<'tcx> Repr<'tcx> for PickKind<'tcx> {
    fn repr(&self, _tcx: &ty::ctxt) -> String {
    }
}

impl<'tcx> Repr<'tcx> for Pick<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
    }
}

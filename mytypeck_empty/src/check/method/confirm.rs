// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::probe;

use check::{self, FnCtxt, NoPreference, PreferMutLvalue, callee, demand};
use check::UnresolvedTypeAction;
use middle::mem_categorization::Typer;
use middle::subst::{self};
use middle::traits;
use middle::ty::{self, Ty};
use middle::ty::{MethodCall, MethodCallee, MethodObject, MethodOrigin,
                 MethodParam, MethodStatic, MethodTraitObject, MethodTypeParam};
use middle::ty_fold::TypeFoldable;
use middle::infer;
use middle::infer::InferCtxt;
use syntax::ast;
use syntax::codemap::Span;
use std::iter::repeat;
use util::ppaux::Repr;

struct ConfirmContext<'a, 'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    self_expr: &'tcx ast::Expr,
    call_expr: &'tcx ast::Expr,
}

struct InstantiatedMethodSig<'tcx> {
    /// Function signature of the method being invoked. The 0th
    /// argument is the receiver.
    method_sig: ty::FnSig<'tcx>,

    /// Substitutions for all types/early-bound-regions declared on
    /// the method.
    all_substs: subst::Substs<'tcx>,

    /// Generic bounds on the method's parameters which must be added
    /// as pending obligations.
    method_predicates: ty::InstantiatedPredicates<'tcx>,
}

pub fn confirm<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                         span: Span,
                         self_expr: &'tcx ast::Expr,
                         call_expr: &'tcx ast::Expr,
                         unadjusted_self_ty: Ty<'tcx>,
                         pick: probe::Pick<'tcx>,
                         supplied_method_types: Vec<Ty<'tcx>>)
                         -> MethodCallee<'tcx>
{
}

impl<'a,'tcx> ConfirmContext<'a,'tcx> {
    fn new(fcx: &'a FnCtxt<'a, 'tcx>,
           span: Span,
           self_expr: &'tcx ast::Expr,
           call_expr: &'tcx ast::Expr)
           -> ConfirmContext<'a, 'tcx>
    {
    }

    fn confirm(&mut self,
               unadjusted_self_ty: Ty<'tcx>,
               pick: probe::Pick<'tcx>,
               supplied_method_types: Vec<Ty<'tcx>>)
               -> MethodCallee<'tcx>
    {
    }

    ///////////////////////////////////////////////////////////////////////////
    // ADJUSTMENTS

    fn adjust_self_ty(&mut self,
                      unadjusted_self_ty: Ty<'tcx>,
                      pick: &probe::Pick<'tcx>)
                      -> Ty<'tcx>
    {
    }

    ///////////////////////////////////////////////////////////////////////////
    //

    /// Returns a set of substitutions for the method *receiver* where all type and region
    /// parameters are instantiated with fresh variables. This substitution does not include any
    /// parameters declared on the method itself.
    ///
    /// Note that this substitution may include late-bound regions from the impl level. If so,
    /// these are instantiated later in the `instantiate_method_sig` routine.
    fn fresh_receiver_substs(&mut self,
                             self_ty: Ty<'tcx>,
                             pick: &probe::Pick<'tcx>)
                             -> (subst::Substs<'tcx>, MethodOrigin<'tcx>)
    {
    }

    fn extract_trait_ref<R, F>(&mut self, self_ty: Ty<'tcx>, mut closure: F) -> R where
        F: FnMut(&mut ConfirmContext<'a, 'tcx>, Ty<'tcx>, &ty::TyTrait<'tcx>) -> R,
    {
    }

    fn unify_receivers(&mut self,
                       self_ty: Ty<'tcx>,
                       method_self_ty: Ty<'tcx>)
    {
    }

    ///////////////////////////////////////////////////////////////////////////
    //

    fn instantiate_method_sig(&mut self,
                              pick: &probe::Pick<'tcx>,
                              all_substs: subst::Substs<'tcx>)
                              -> InstantiatedMethodSig<'tcx>
    {
    }

    fn add_obligations(&mut self,
                       pick: &probe::Pick<'tcx>,
                       all_substs: &subst::Substs<'tcx>,
                       method_predicates: &ty::InstantiatedPredicates<'tcx>) {
    }

    ///////////////////////////////////////////////////////////////////////////
    // RECONCILIATION

    /// When we select a method with an `&mut self` receiver, we have to go convert any
    /// auto-derefs, indices, etc from `Deref` and `Index` into `DerefMut` and `IndexMut`
    /// respectively.
    fn fixup_derefs_on_method_receiver_if_necessary(&self,
                                                    method_callee: &MethodCallee) {
    }

    ///////////////////////////////////////////////////////////////////////////
    // MISCELLANY

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
    }

    fn infcx(&self) -> &'a InferCtxt<'a, 'tcx> {
    }

    fn enforce_illegal_method_limitations(&self, pick: &probe::Pick) {
    }

    fn upcast(&mut self,
              source_trait_ref: ty::PolyTraitRef<'tcx>,
              target_trait_def_id: ast::DefId)
              -> ty::PolyTraitRef<'tcx>
    {
    }

    fn replace_late_bound_regions_with_fresh_var<T>(&self, value: &ty::Binder<T>) -> T
        where T : TypeFoldable<'tcx> + Repr<'tcx>
    {
    }
}

// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use astconv::AstConv;
use check::{FnCtxt, Inherited, blank_fn_ctxt, regionck};
use constrained_type_params::{identify_constrained_type_params, Parameter};
use CrateCtxt;
use middle::region;
use middle::subst::{self, TypeSpace, FnSpace, ParamSpace, SelfSpace};
use middle::traits;
use middle::ty::{self, Ty};
use middle::ty::liberate_late_bound_regions;
use middle::ty_fold::{TypeFolder, TypeFoldable, super_fold_ty};
use util::ppaux::{Repr, UserString};

use std::collections::HashSet;
use syntax::ast;
use syntax::ast_util::local_def;
use syntax::codemap::Span;
use syntax::parse::token::{self, special_idents};
use syntax::visit;
use syntax::visit::Visitor;

pub struct CheckTypeWellFormedVisitor<'ccx, 'tcx:'ccx> {
    ccx: &'ccx CrateCtxt<'ccx, 'tcx>,
    cache: HashSet<Ty<'tcx>>
}

impl<'ccx, 'tcx> CheckTypeWellFormedVisitor<'ccx, 'tcx> {
    pub fn new(ccx: &'ccx CrateCtxt<'ccx, 'tcx>) -> CheckTypeWellFormedVisitor<'ccx, 'tcx> {
    }

    fn tcx(&self) -> &ty::ctxt<'tcx> {
    }

    /// Checks that the field types (in a struct def'n) or argument types (in an enum def'n) are
    /// well-formed, meaning that they do not require any constraints not declared in the struct
    /// definition itself. For example, this definition would be illegal:
    ///
    ///     struct Ref<'a, T> { x: &'a T }
    ///
    /// because the type did not declare that `T:'a`.
    ///
    /// We do this check as a pre-pass before checking fn bodies because if these constraints are
    /// not included it frequently leads to confusing errors in fn bodies. So it's better to check
    /// the types first.
    fn check_item_well_formed(&mut self, item: &ast::Item) {
    }

    fn with_fcx<F>(&mut self, item: &ast::Item, mut f: F) where
        F: for<'fcx> FnMut(&mut CheckTypeWellFormedVisitor<'ccx, 'tcx>, &FnCtxt<'fcx, 'tcx>),
    {
    }

    /// In a type definition, we check that to ensure that the types of the fields are well-formed.
    fn check_type_defn<F>(&mut self, item: &ast::Item, mut lookup_fields: F) where
        F: for<'fcx> FnMut(&FnCtxt<'fcx, 'tcx>) -> Vec<AdtVariant<'tcx>>,
    {
    }

    fn check_item_type(&mut self,
                       item: &ast::Item)
    {
    }

    fn check_impl(&mut self,
                  item: &ast::Item)
    {
    }

    fn check_variances_for_type_defn(&self,
                                     item: &ast::Item,
                                     ast_generics: &ast::Generics)
    {
    }

    fn param_ty(&self,
                ast_generics: &ast::Generics,
                space: ParamSpace,
                index: usize)
                -> ty::ParamTy
    {
    }

    fn ty_param_span(&self,
                     ast_generics: &ast::Generics,
                     item: &ast::Item,
                     space: ParamSpace,
                     index: usize)
                     -> Span
    {
    }

    fn report_bivariance(&self,
                         span: Span,
                         param_name: ast::Name)
    {
    }
}

// Reject any predicates that do not involve a type parameter.
fn reject_non_type_param_bounds<'tcx>(tcx: &ty::ctxt<'tcx>,
                                      span: Span,
                                      predicates: &ty::GenericPredicates<'tcx>) {
}

fn reject_shadowing_type_parameters<'tcx>(tcx: &ty::ctxt<'tcx>,
                                          span: Span,
                                          generics: &ty::Generics<'tcx>) {
}

impl<'ccx, 'tcx, 'v> Visitor<'v> for CheckTypeWellFormedVisitor<'ccx, 'tcx> {
    fn visit_item(&mut self, i: &ast::Item) {
    }

    fn visit_fn(&mut self,
                fk: visit::FnKind<'v>, fd: &'v ast::FnDecl,
                b: &'v ast::Block, span: Span, id: ast::NodeId) {
    }

    fn visit_trait_item(&mut self, trait_item: &'v ast::TraitItem) {
    }
}

pub struct BoundsChecker<'cx,'tcx:'cx> {
    fcx: &'cx FnCtxt<'cx,'tcx>,
    span: Span,

    // This field is often attached to item impls; it is not clear
    // that `CodeExtent` is well-defined for such nodes, so pnkfelix
    // has left it as a NodeId rather than porting to CodeExtent.
    scope: ast::NodeId,

    binding_count: usize,
    cache: Option<&'cx mut HashSet<Ty<'tcx>>>,
}

impl<'cx,'tcx> BoundsChecker<'cx,'tcx> {
    pub fn new(fcx: &'cx FnCtxt<'cx,'tcx>,
               span: Span,
               scope: ast::NodeId,
               cache: Option<&'cx mut HashSet<Ty<'tcx>>>)
               -> BoundsChecker<'cx,'tcx> {
    }

    /// Given a trait ref like `A : Trait<B>`, where `Trait` is defined as (say):
    ///
    ///     trait Trait<B:OtherTrait> : Copy { ... }
    ///
    /// This routine will check that `B : OtherTrait` and `A : Trait<B>`. It will also recursively
    /// check that the types `A` and `B` are well-formed.
    ///
    /// Note that it does not (currently, at least) check that `A : Copy` (that check is delegated
    /// to the point where impl `A : Trait<B>` is implemented).
    pub fn check_trait_ref(&mut self, trait_ref: &ty::TraitRef<'tcx>) {
    }

    pub fn check_ty(&mut self, ty: Ty<'tcx>) {
    }

    fn check_traits_in_ty(&mut self, ty: Ty<'tcx>) {
    }
}

impl<'cx,'tcx> TypeFolder<'tcx> for BoundsChecker<'cx,'tcx> {
    fn tcx(&self) -> &ty::ctxt<'tcx> {
    }

    fn fold_binder<T>(&mut self, binder: &ty::Binder<T>) -> ty::Binder<T>
        where T : TypeFoldable<'tcx> + Repr<'tcx>
    {
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
    }
}

///////////////////////////////////////////////////////////////////////////
// ADT

struct AdtVariant<'tcx> {
    fields: Vec<AdtField<'tcx>>,
}

struct AdtField<'tcx> {
    ty: Ty<'tcx>,
    span: Span,
}

fn struct_variant<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                            struct_def: &ast::StructDef)
                            -> AdtVariant<'tcx> {
}

fn enum_variants<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                           enum_def: &ast::EnumDef)
                           -> Vec<AdtVariant<'tcx>> {
}

fn filter_to_trait_obligations<'tcx>(bounds: ty::InstantiatedPredicates<'tcx>)
                                     -> ty::InstantiatedPredicates<'tcx>
{
}

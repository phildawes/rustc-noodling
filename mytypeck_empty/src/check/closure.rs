// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code for type-checking closure expressions.

use super::{check_fn, Expectation, FnCtxt};

use astconv;
use middle::region;
use middle::subst;
use middle::ty::{self, ToPolyTraitRef, Ty};
use std::cmp;
use syntax::abi;
use syntax::ast;
use syntax::ast_util;
use util::ppaux::Repr;

pub fn check_expr_closure<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                                   expr: &ast::Expr,
                                   _capture: ast::CaptureClause,
                                   decl: &'tcx ast::FnDecl,
                                   body: &'tcx ast::Block,
                                   expected: Expectation<'tcx>) {
}

fn check_closure<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                          expr: &ast::Expr,
                          opt_kind: Option<ty::ClosureKind>,
                          decl: &'tcx ast::FnDecl,
                          body: &'tcx ast::Block,
                          expected_sig: Option<ty::FnSig<'tcx>>) {
}

fn deduce_expectations_from_expected_type<'a,'tcx>(
    fcx: &FnCtxt<'a,'tcx>,
    expected_ty: Ty<'tcx>)
    -> (Option<ty::FnSig<'tcx>>,Option<ty::ClosureKind>)
{
}

fn deduce_expectations_from_obligations<'a,'tcx>(
    fcx: &FnCtxt<'a,'tcx>,
    expected_vid: ty::TyVid)
    -> (Option<ty::FnSig<'tcx>>, Option<ty::ClosureKind>)
{
}

fn pick_most_restrictive_closure_kind(best: Option<ty::ClosureKind>,
                                      cur: ty::ClosureKind)
                                      -> Option<ty::ClosureKind>
{
}

/// Given a projection like "<F as Fn(X)>::Result == Y", we can deduce
/// everything we need to know about a closure.
fn deduce_sig_from_projection<'a,'tcx>(
    fcx: &FnCtxt<'a,'tcx>,
    projection: &ty::PolyProjectionPredicate<'tcx>)
    -> Option<ty::FnSig<'tcx>>
{
}

fn self_type_matches_expected_vid<'a,'tcx>(
    fcx: &FnCtxt<'a,'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
    expected_vid: ty::TyVid)
    -> Option<ty::PolyTraitRef<'tcx>>
{
}

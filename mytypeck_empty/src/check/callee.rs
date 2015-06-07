// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::autoderef;
use super::check_argument_types;
use super::check_expr;
use super::check_method_argument_types;
use super::demand;
use super::DeferredCallResolution;
use super::err_args;
use super::Expectation;
use super::expected_types_for_fn_args;
use super::FnCtxt;
use super::LvaluePreference;
use super::method;
use super::structurally_resolved_type;
use super::TupleArgumentsFlag;
use super::UnresolvedTypeAction;
use super::write_call;

use CrateCtxt;
use middle::infer;
use middle::ty::{self, Ty, ClosureTyper};
use syntax::ast;
use syntax::codemap::Span;
use syntax::parse::token;
use syntax::ptr::P;
use util::ppaux::Repr;

/// Check that it is legal to call methods of the trait corresponding
/// to `trait_id` (this only cares about the trait, not the specific
/// method that is called)
pub fn check_legal_trait_for_method_call(ccx: &CrateCtxt, span: Span, trait_id: ast::DefId) {
}

pub fn check_call<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                            call_expr: &'tcx ast::Expr,
                            callee_expr: &'tcx ast::Expr,
                            arg_exprs: &'tcx [P<ast::Expr>],
                            expected: Expectation<'tcx>)
{
}

enum CallStep<'tcx> {
    Builtin,
    DeferredClosure(ty::FnSig<'tcx>),
    Overloaded(ty::MethodCallee<'tcx>)
}

fn try_overloaded_call_step<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                      call_expr: &'tcx ast::Expr,
                                      callee_expr: &'tcx ast::Expr,
                                      adjusted_ty: Ty<'tcx>,
                                      autoderefs: usize)
                                      -> Option<CallStep<'tcx>>
{
}

fn try_overloaded_call_traits<'a,'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                       call_expr: &ast::Expr,
                                       callee_expr: &ast::Expr,
                                       adjusted_ty: Ty<'tcx>,
                                       autoderefs: usize)
                                       -> Option<ty::MethodCallee<'tcx>>
{
}

fn confirm_builtin_call<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                                 call_expr: &ast::Expr,
                                 callee_ty: Ty<'tcx>,
                                 arg_exprs: &'tcx [P<ast::Expr>],
                                 expected: Expectation<'tcx>)
{
}

fn confirm_deferred_closure_call<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                                          call_expr: &ast::Expr,
                                          arg_exprs: &'tcx [P<ast::Expr>],
                                          expected: Expectation<'tcx>,
                                          fn_sig: ty::FnSig<'tcx>)
{
}

fn confirm_overloaded_call<'a,'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                    call_expr: &ast::Expr,
                                    callee_expr: &'tcx ast::Expr,
                                    arg_exprs: &'tcx [P<ast::Expr>],
                                    expected: Expectation<'tcx>,
                                    method_callee: ty::MethodCallee<'tcx>)
{
}

fn write_overloaded_call_method_map<'a,'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                             call_expr: &ast::Expr,
                                             method_callee: ty::MethodCallee<'tcx>) {
}

struct CallResolution<'tcx> {
    call_expr: &'tcx ast::Expr,
    callee_expr: &'tcx ast::Expr,
    adjusted_ty: Ty<'tcx>,
    autoderefs: usize,
    fn_sig: ty::FnSig<'tcx>,
    closure_def_id: ast::DefId,
}

impl<'tcx> Repr<'tcx> for CallResolution<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
    }
}

impl<'tcx> DeferredCallResolution<'tcx> for CallResolution<'tcx> {
    fn resolve<'a>(&mut self, fcx: &FnCtxt<'a,'tcx>) {
    }
}

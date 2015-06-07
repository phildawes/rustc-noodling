// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code related to processing overloaded binary and unary operators.

use super::{
    check_expr,
    check_expr_coercable_to_type,
    check_expr_with_lvalue_pref,
    demand,
    method,
    FnCtxt,
    PreferMutLvalue,
    structurally_resolved_type,
};
use middle::traits;
use middle::ty::{self, Ty};
use syntax::ast;
use syntax::ast_util;
use syntax::parse::token;
use util::ppaux::{Repr, UserString};

/// Check a `a <op>= b`
pub fn check_binop_assign<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                                   expr: &'tcx ast::Expr,
                                   op: ast::BinOp,
                                   lhs_expr: &'tcx ast::Expr,
                                   rhs_expr: &'tcx ast::Expr)
{
}

/// Check a potentially overloaded binary operator.
pub fn check_binop<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                             expr: &'tcx ast::Expr,
                             op: ast::BinOp,
                             lhs_expr: &'tcx ast::Expr,
                             rhs_expr: &'tcx ast::Expr)
{
}

fn enforce_builtin_binop_types<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                         lhs_expr: &'tcx ast::Expr,
                                         lhs_ty: Ty<'tcx>,
                                         rhs_expr: &'tcx ast::Expr,
                                         rhs_ty: Ty<'tcx>,
                                         op: ast::BinOp)
                                         -> Ty<'tcx>
{
}

fn check_overloaded_binop<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                    expr: &'tcx ast::Expr,
                                    lhs_expr: &'tcx ast::Expr,
                                    lhs_ty: Ty<'tcx>,
                                    rhs_expr: &'tcx ast::Expr,
                                    op: ast::BinOp)
                                    -> (Ty<'tcx>, Ty<'tcx>)
{
}

pub fn check_user_unop<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                 op_str: &str,
                                 mname: &str,
                                 trait_did: Option<ast::DefId>,
                                 ex: &'tcx ast::Expr,
                                 operand_expr: &'tcx ast::Expr,
                                 operand_ty: Ty<'tcx>,
                                 op: ast::UnOp)
                                 -> Ty<'tcx>
{
}

fn name_and_trait_def_id(fcx: &FnCtxt, op: ast::BinOp) -> (&'static str, Option<ast::DefId>) {
}

fn lookup_op_method<'a, 'tcx>(fcx: &'a FnCtxt<'a, 'tcx>,
                              expr: &'tcx ast::Expr,
                              lhs_ty: Ty<'tcx>,
                              other_tys: Vec<Ty<'tcx>>,
                              opname: ast::Name,
                              trait_did: Option<ast::DefId>,
                              lhs_expr: &'a ast::Expr)
                              -> Result<Ty<'tcx>,()>
{
}

// Binary operator categories. These categories summarize the behavior
// with respect to the builtin operationrs supported.
enum BinOpCategory {
    /// &&, || -- cannot be overridden
    Shortcircuit,

    /// <<, >> -- when shifting a single integer, rhs can be any
    /// integer type. For simd, types must match.
    Shift,

    /// +, -, etc -- takes equal types, produces same type as input,
    /// applicable to ints/floats/simd
    Math,

    /// &, |, ^ -- takes equal types, produces same type as input,
    /// applicable to ints/floats/simd/bool
    Bitwise,

    /// ==, !=, etc -- takes equal types, produces bools, except for simd,
    /// which produce the input type
    Comparison,
}

impl BinOpCategory {
    fn from(op: ast::BinOp) -> BinOpCategory {
    }
}

/// Returns true if this is a built-in arithmetic operation (e.g. u32
/// + u32, i16x4 == i16x4) and false if these types would have to be
/// overloaded to be legal. There are two reasons that we distinguish
/// builtin operations from overloaded ones (vs trying to drive
/// everything uniformly through the trait system and intrinsics or
/// something like that):
///
/// 1. Builtin operations can trivially be evaluated in constants.
/// 2. For comparison operators applied to SIMD types the result is
///    not of type `bool`. For example, `i16x4==i16x4` yields a
///    type like `i16x4`. This means that the overloaded trait
///    `PartialEq` is not applicable.
///
/// Reason #2 is the killer. I tried for a while to always use
/// overloaded logic and just check the types in constants/trans after
/// the fact, and it worked fine, except for SIMD types. -nmatsakis
fn is_builtin_binop<'tcx>(cx: &ty::ctxt<'tcx>,
                          lhs: Ty<'tcx>,
                          rhs: Ty<'tcx>,
                          op: ast::BinOp)
                          -> bool
{
}


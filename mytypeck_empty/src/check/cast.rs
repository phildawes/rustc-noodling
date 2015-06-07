// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code for type-checking cast expressions.
//!
//! A cast `e as U` is valid if one of the following holds:
//! * `e` has type `T` and `T` coerces to `U`; *coercion-cast*
//! * `e` has type `*T`, `U` is `*U_0`, and either `U_0: Sized` or
//!    unsize_kind(`T`) = unsize_kind(`U_0`); *ptr-ptr-cast*
//! * `e` has type `*T` and `U` is a numeric type, while `T: Sized`; *ptr-addr-cast*
//! * `e` is an integer and `U` is `*U_0`, while `U_0: Sized`; *addr-ptr-cast*
//! * `e` has type `T` and `T` and `U` are any numeric types; *numeric-cast*
//! * `e` is a C-like enum and `U` is an integer type; *enum-cast*
//! * `e` has type `bool` or `char` and `U` is an integer; *prim-int-cast*
//! * `e` has type `u8` and `U` is `char`; *u8-char-cast*
//! * `e` has type `&[T; n]` and `U` is `*const T`; *array-ptr-cast*
//! * `e` is a function pointer type and `U` has type `*T`,
//!   while `T: Sized`; *fptr-ptr-cast*
//! * `e` is a function pointer type and `U` is an integer; *fptr-addr-cast*
//!
//! where `&.T` and `*T` are references of either mutability,
//! and where unsize_kind(`T`) is the kind of the unsize info
//! in `T` - a vtable or a length (or `()` if `T: Sized`).
//!
//! Casting is not transitive, that is, even if `e as U1 as U2` is a valid
//! expression, `e as U2` is not necessarily so (in fact it will only be valid if
//! `U1` coerces to `U2`).

use super::coercion;
use super::demand;
use super::FnCtxt;
use super::structurally_resolved_type;

use lint;
use middle::cast::{CastKind, CastTy};
use middle::ty;
use middle::ty::Ty;
use syntax::ast;
use syntax::ast::UintTy::{TyU8};
use syntax::codemap::Span;
use util::ppaux::Repr;

/// Reifies a cast check to be checked once we have full type information for
/// a function context.
pub struct CastCheck<'tcx> {
    expr: ast::Expr,
    expr_ty: Ty<'tcx>,
    cast_ty: Ty<'tcx>,
    span: Span,
}

/// The kind of the unsize info (length or vtable) - we only allow casts between
/// fat pointers if their unsize-infos have the same kind.
#[derive(Copy, Clone, PartialEq, Eq)]
enum UnsizeKind<'tcx> {
    Vtable,
    Length,
    /// The unsize info of this projection
    OfProjection(&'tcx ty::ProjectionTy<'tcx>),
    /// The unsize info of this parameter
    OfParam(&'tcx ty::ParamTy)
}

/// Returns the kind of unsize information of t, or None
/// if t is sized or it is unknown.
fn unsize_kind<'a,'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                        t: Ty<'tcx>)
                        -> Option<UnsizeKind<'tcx>> {
}

#[derive(Copy, Clone)]
enum CastError {
    CastToBool,
    CastToChar,
    DifferingKinds,
    IllegalCast,
    NeedViaPtr,
    NeedViaInt,
    NeedViaUsize,
    NonScalar,
    RefToMutPtr
}

impl<'tcx> CastCheck<'tcx> {
    pub fn new(expr: ast::Expr, expr_ty: Ty<'tcx>, cast_ty: Ty<'tcx>, span: Span)
               -> CastCheck<'tcx> {
    }

    fn report_cast_error<'a>(&self, fcx: &FnCtxt<'a, 'tcx>,
                             e: CastError) {
    }

    fn trivial_cast_lint<'a>(&self, fcx: &FnCtxt<'a, 'tcx>) {
    }

    pub fn check<'a>(mut self, fcx: &FnCtxt<'a, 'tcx>) {
    }

    /// Check a cast, and report an error if one exists. In some cases, this
    /// can return Ok and create type errors in the fcx rather than returning
    /// directly. coercion-cast is handled in check instead of here.
    fn do_check<'a>(&self, fcx: &FnCtxt<'a, 'tcx>) -> Result<CastKind, CastError> {
    }

    fn check_ptr_ptr_cast<'a>(&self,
                              fcx: &FnCtxt<'a, 'tcx>,
                              m_expr: &'tcx ty::mt<'tcx>,
                              m_cast: &'tcx ty::mt<'tcx>)
                              -> Result<CastKind, CastError>
    {
    }

    fn check_fptr_ptr_cast<'a>(&self,
                               fcx: &FnCtxt<'a, 'tcx>,
                               m_cast: &'tcx ty::mt<'tcx>)
                               -> Result<CastKind, CastError>
    {
    }

    fn check_ptr_addr_cast<'a>(&self,
                               fcx: &FnCtxt<'a, 'tcx>,
                               m_expr: &'tcx ty::mt<'tcx>)
                               -> Result<CastKind, CastError>
    {
    }

    fn check_ref_cast<'a>(&self,
                          fcx: &FnCtxt<'a, 'tcx>,
                          m_expr: &'tcx ty::mt<'tcx>,
                          m_cast: &'tcx ty::mt<'tcx>)
                          -> Result<CastKind, CastError>
    {
    }

    fn check_addr_ptr_cast<'a>(&self,
                               fcx: &FnCtxt<'a, 'tcx>,
                               m_cast: &'tcx ty::mt<'tcx>)
                               -> Result<CastKind, CastError>
    {
    }

    fn try_coercion_cast<'a>(&self, fcx: &FnCtxt<'a, 'tcx>) -> bool {
    }

}

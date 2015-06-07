// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


use check::{coercion, FnCtxt};
use middle::ty::{self, Ty};
use middle::infer;

use std::result::Result::{Err, Ok};
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

// Requires that the two types unify, and prints an error message if
// they don't.
pub fn suptype<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, sp: Span,
                         ty_expected: Ty<'tcx>, ty_actual: Ty<'tcx>) {
}

/// As `suptype`, but call `handle_err` if unification for subtyping fails.
pub fn suptype_with_fn<'a, 'tcx, F>(fcx: &FnCtxt<'a, 'tcx>,
                                    sp: Span,
                                    b_is_expected: bool,
                                    ty_a: Ty<'tcx>,
                                    ty_b: Ty<'tcx>,
                                    handle_err: F) where
    F: FnOnce(Span, Ty<'tcx>, Ty<'tcx>, &ty::type_err<'tcx>),
{
}

pub fn eqtype<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, sp: Span,
                        expected: Ty<'tcx>, actual: Ty<'tcx>) {
}

// Checks that the type of `expr` can be coerced to `expected`.
pub fn coerce<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                        sp: Span,
                        expected: Ty<'tcx>,
                        expr: &ast::Expr) {
}

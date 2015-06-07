// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::const_eval;
use middle::def;
use middle::infer;
use middle::pat_util::{PatIdMap, pat_id_map, pat_is_binding};
use middle::pat_util::pat_is_resolved_const;
use middle::privacy::{AllPublic, LastMod};
use middle::subst::Substs;
use middle::ty::{self, Ty};
use check::{check_expr, check_expr_has_type, check_expr_with_expectation};
use check::{check_expr_coercable_to_type, demand, FnCtxt, Expectation};
use check::{instantiate_path, resolve_ty_and_def_ufcs, structurally_resolved_type};
use require_same_types;
use util::nodemap::FnvHashMap;
use util::ppaux::Repr;

use std::cmp::{self, Ordering};
use std::collections::hash_map::Entry::{Occupied, Vacant};
use syntax::ast;
use syntax::ast_util;
use syntax::codemap::{Span, Spanned};
use syntax::parse::token;
use syntax::print::pprust;
use syntax::ptr::P;

pub fn check_pat<'a, 'tcx>(pcx: &pat_ctxt<'a, 'tcx>,
                           pat: &'tcx ast::Pat,
                           expected: Ty<'tcx>)
{
}

fn check_assoc_item_is_const(pcx: &pat_ctxt, def: def::Def, span: Span) -> bool {
}

pub fn check_dereferencable<'a, 'tcx>(pcx: &pat_ctxt<'a, 'tcx>,
                                      span: Span, expected: Ty<'tcx>,
                                      inner: &ast::Pat) -> bool {
}

pub fn check_match<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                             expr: &'tcx ast::Expr,
                             discrim: &'tcx ast::Expr,
                             arms: &'tcx [ast::Arm],
                             expected: Expectation<'tcx>,
                             match_src: ast::MatchSource) {
}

pub struct pat_ctxt<'a, 'tcx: 'a> {
    pub fcx: &'a FnCtxt<'a, 'tcx>,
    pub map: PatIdMap,
}

pub fn check_pat_struct<'a, 'tcx>(pcx: &pat_ctxt<'a, 'tcx>, pat: &'tcx ast::Pat,
                                  path: &ast::Path, fields: &'tcx [Spanned<ast::FieldPat>],
                                  etc: bool, expected: Ty<'tcx>) {
}

pub fn check_pat_enum<'a, 'tcx>(pcx: &pat_ctxt<'a, 'tcx>,
                                pat: &ast::Pat,
                                path: &ast::Path,
                                subpats: Option<&'tcx [P<ast::Pat>]>,
                                expected: Ty<'tcx>)
{
}

/// `path` is the AST path item naming the type of this struct.
/// `fields` is the field patterns of the struct pattern.
/// `struct_fields` describes the type of each field of the struct.
/// `struct_id` is the ID of the struct.
/// `etc` is true if the pattern said '...' and false otherwise.
pub fn check_struct_pat_fields<'a, 'tcx>(pcx: &pat_ctxt<'a, 'tcx>,
                                         span: Span,
                                         fields: &'tcx [Spanned<ast::FieldPat>],
                                         struct_fields: &[ty::field<'tcx>],
                                         struct_id: ast::DefId,
                                         etc: bool) {
}

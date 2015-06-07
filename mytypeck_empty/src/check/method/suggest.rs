// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Give useful errors and suggestions to users when an item can't be
//! found or is otherwise invalid.

use CrateCtxt;

use astconv::AstConv;
use check::{self, FnCtxt};
use middle::ty::{self, Ty};
use middle::def;
use metadata::{csearch, cstore, decoder};
use util::ppaux::UserString;

use syntax::{ast, ast_util};
use syntax::codemap::Span;
use syntax::print::pprust;

use std::cell;
use std::cmp::Ordering;

use super::{MethodError, CandidateSource, impl_item, trait_item};
use super::probe::Mode;

pub fn report_error<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                              span: Span,
                              rcvr_ty: Ty<'tcx>,
                              item_name: ast::Name,
                              rcvr_expr: Option<&ast::Expr>,
                              error: MethodError)
{
}


pub type AllTraitsVec = Vec<TraitInfo>;

fn suggest_traits_to_import<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                      span: Span,
                                      rcvr_ty: Ty<'tcx>,
                                      item_name: ast::Name,
                                      rcvr_expr: Option<&ast::Expr>,
                                      valid_out_of_scope_traits: Vec<ast::DefId>)
{
}

/// Checks whether there is a local type somewhere in the chain of
/// autoderefs of `rcvr_ty`.
fn type_derefs_to_local<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                  span: Span,
                                  rcvr_ty: Ty<'tcx>,
                                  rcvr_expr: Option<&ast::Expr>) -> bool {
}

#[derive(Copy, Clone)]
pub struct TraitInfo {
    pub def_id: ast::DefId,
}

impl TraitInfo {
    fn new(def_id: ast::DefId) -> TraitInfo {
        TraitInfo {
            def_id: def_id,
        }
    }
}
impl PartialEq for TraitInfo {
    fn eq(&self, other: &TraitInfo) -> bool {
    }
}
impl Eq for TraitInfo {}
impl PartialOrd for TraitInfo {
    fn partial_cmp(&self, other: &TraitInfo) -> Option<Ordering> { }
}
impl Ord for TraitInfo {
    fn cmp(&self, other: &TraitInfo) -> Ordering {
    }
}

/// Retrieve all traits in this crate and any dependent crates.
pub fn all_traits<'a>(ccx: &'a CrateCtxt) -> AllTraits<'a> {
}

pub struct AllTraits<'a> {
    borrow: cell::Ref<'a, Option<AllTraitsVec>>,
    idx: usize
}

impl<'a> Iterator for AllTraits<'a> {
    type Item = TraitInfo;

    fn next(&mut self) -> Option<TraitInfo> {
    }
}

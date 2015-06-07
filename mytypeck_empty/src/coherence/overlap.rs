// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Overlap: No two impls for the same trait are implemented for the
//! same type.

use middle::traits;
use middle::ty;
use middle::infer::{self, new_infer_ctxt};
use syntax::ast::DefId;
use syntax::ast::LOCAL_CRATE;
use syntax::ast;
use syntax::ast_util;
use syntax::visit;
use syntax::codemap::Span;
use util::nodemap::DefIdMap;
use util::ppaux::{Repr, UserString};

pub fn check(tcx: &ty::ctxt) {
}

struct OverlapChecker<'cx, 'tcx:'cx> {
    tcx: &'cx ty::ctxt<'tcx>,

    // maps from a trait def-id to an impl id
    default_impls: DefIdMap<ast::NodeId>,
}

impl<'cx, 'tcx> OverlapChecker<'cx, 'tcx> {
    fn check_for_overlapping_impls(&self) {
    }

    fn check_for_overlapping_impls_of_trait(&self,
                                            trait_def: &'tcx ty::TraitDef<'tcx>)
    {
    }

    // We need to coherently pick which impl will be displayed
    // as causing the error message, and it must be the in the current
    // crate. Just pick the smaller impl in the file.
    fn order_impls(&self, impl1_def_id: ast::DefId, impl2_def_id: ast::DefId)
            -> Option<(ast::DefId, ast::DefId)> {
    }


    fn check_if_impls_overlap(&self,
                              trait_def_id: ast::DefId,
                              impl1_def_id: ast::DefId,
                              impl2_def_id: ast::DefId)
    {
    }

    fn report_overlap_error(&self, trait_def_id: ast::DefId,
                            impl1: ast::DefId, impl2: ast::DefId) {
    }

    fn report_overlap_note(&self, impl1: ast::DefId, impl2: ast::DefId) {
    }

    fn span_of_impl(&self, impl_did: ast::DefId) -> Span {
    }
}


impl<'cx, 'tcx,'v> visit::Visitor<'v> for OverlapChecker<'cx, 'tcx> {
    fn visit_item(&mut self, item: &'v ast::Item) {
    }
}

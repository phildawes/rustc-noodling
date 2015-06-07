// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Unsafety checker: every impl either implements a trait defined in this
//! crate or pertains to a type defined in this crate.

use middle::ty;
use syntax::ast::{Item, ItemImpl};
use syntax::ast;
use syntax::ast_util;
use syntax::visit;
use util::ppaux::UserString;

pub fn check(tcx: &ty::ctxt) {
}

struct UnsafetyChecker<'cx, 'tcx:'cx> {
    tcx: &'cx ty::ctxt<'tcx>
}

impl<'cx, 'tcx, 'v> UnsafetyChecker<'cx, 'tcx> {
    fn check_unsafety_coherence(&mut self, item: &'v ast::Item,
                                unsafety: ast::Unsafety,
                                polarity: ast::ImplPolarity) {
    }
}

impl<'cx, 'tcx,'v> visit::Visitor<'v> for UnsafetyChecker<'cx, 'tcx> {
    fn visit_item(&mut self, item: &'v ast::Item) {
    }
}

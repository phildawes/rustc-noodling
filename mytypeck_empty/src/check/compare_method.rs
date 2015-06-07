// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::free_region::FreeRegionMap;
use middle::infer;
use middle::traits;
use middle::ty::{self};
use middle::subst::{self, Subst, Substs, VecPerParamSpace};
use util::ppaux::{self, Repr};

use syntax::ast;
use syntax::codemap::Span;
use syntax::parse::token;

use super::assoc;

/// Checks that a method from an impl conforms to the signature of
/// the same method as declared in the trait.
///
/// # Parameters
///
/// - impl_m: type of the method we are checking
/// - impl_m_span: span to use for reporting errors
/// - impl_m_body_id: id of the method body
/// - trait_m: the method in the trait
/// - impl_trait_ref: the TraitRef corresponding to the trait implementation

pub fn compare_impl_method<'tcx>(tcx: &ty::ctxt<'tcx>,
                                 impl_m: &ty::Method<'tcx>,
                                 impl_m_span: Span,
                                 impl_m_body_id: ast::NodeId,
                                 trait_m: &ty::Method<'tcx>,
                                 impl_trait_ref: &ty::TraitRef<'tcx>) {
}

pub fn compare_const_impl<'tcx>(tcx: &ty::ctxt<'tcx>,
                                impl_c: &ty::AssociatedConst<'tcx>,
                                impl_c_span: Span,
                                trait_c: &ty::AssociatedConst<'tcx>,
                                impl_trait_ref: &ty::TraitRef<'tcx>) {
}

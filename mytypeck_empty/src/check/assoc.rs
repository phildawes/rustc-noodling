// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::infer::InferCtxt;
use middle::traits::{self, FulfillmentContext, Normalized, MiscObligation,
                     SelectionContext, ObligationCause};
use middle::ty::{self, HasProjectionTypes};
use middle::ty_fold::{TypeFoldable, TypeFolder};
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

pub fn normalize_associated_types_in<'a,'tcx,T>(infcx: &InferCtxt<'a,'tcx>,
                                                typer: &(ty::ClosureTyper<'tcx>+'a),
                                                fulfillment_cx: &mut FulfillmentContext<'tcx>,
                                                span: Span,
                                                body_id: ast::NodeId,
                                                value: &T)
                                                -> T
    where T : TypeFoldable<'tcx> + HasProjectionTypes + Clone + Repr<'tcx>
{
}
// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

typeck.rs, an introduction

The type checker is responsible for:

1. Determining the type of each expression
2. Resolving methods and traits
3. Guaranteeing that most type rules are met ("most?", you say, "why most?"
   Well, dear reader, read on)

The main entry point is `check_crate()`.  Type checking operates in
several major phases:

1. The collect phase first passes over all items and determines their
   type, without examining their "innards".

2. Variance inference then runs to compute the variance of each parameter

3. Coherence checks for overlapping or orphaned impls

4. Finally, the check phase then checks function bodies and so forth.
   Within the check phase, we check each function body one at a time
   (bodies of function expressions are checked as part of the
   containing function).  Inference is used to supply types wherever
   they are unknown. The actual checking of a function itself has
   several phases (check, regionck, writeback), as discussed in the
   documentation for the `check` module.

The type checker is defined into various submodules which are documented
independently:

- astconv: converts the AST representation of types
  into the `ty` representation

- collect: computes the types of each top-level item and enters them into
  the `cx.tcache` table for later use

- coherence: enforces coherence rules, builds some tables

- variance: variance inference

- check: walks over function bodies and type checks them, inferring types for
  local variables, type parameters, etc as necessary.

- infer: finds the types to use for each type variable such that
  all subtyping and assignment constraints are met.  In essence, the check
  module specifies the constraints, and the infer module solves them.

# Note

This API is completely unstable and subject to change.

*/
// Do not remove on snapshot creation. Needed for bootstrap. (Issue #22364)
#![cfg_attr(stage0, feature(custom_attribute))]
#![crate_name = "mytypeck"]
#![unstable(feature = "rustc_private")]
#![staged_api]
#![crate_type = "dylib"]
#![crate_type = "rlib"]
#![doc(html_logo_url = "http://www.rust-lang.org/logos/rust-logo-128x128-blk-v2.png",
      html_favicon_url = "https://doc.rust-lang.org/favicon.ico",
      html_root_url = "http://doc.rust-lang.org/nightly/")]

#![allow(non_camel_case_types)]

#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(collections, collections_drain)]
#![feature(core)]
#![feature(quote)]
#![feature(rustc_diagnostic_macros)]
#![feature(rustc_private)]
#![feature(staged_api)]

#[macro_use] extern crate log;
#[macro_use] extern crate syntax;

extern crate arena;
extern crate fmt_macros;
extern crate rustc;

pub use rustc::lint;
pub use rustc::metadata;
pub use rustc::middle;
pub use rustc::session;
pub use rustc::util;

use middle::def;
use middle::infer;
use middle::subst;
use middle::ty::{self, Ty};
use session::config;
use util::common::time;
use util::ppaux::Repr;
use util::ppaux;

use syntax::codemap::Span;
use syntax::print::pprust::*;
use syntax::{ast, ast_map, abi};
use syntax::ast_util::local_def;

use std::cell::RefCell;

// NB: This module needs to be declared first so diagnostics are
// registered before they are used.
pub mod diagnostics;

pub mod check;
mod rscope;
mod astconv;
pub mod collect;
mod constrained_type_params;
pub mod coherence;
pub mod variance;

pub struct TypeAndSubsts<'tcx> {
    pub substs: subst::Substs<'tcx>,
    pub ty: Ty<'tcx>,
}

pub struct CrateCtxt<'a, 'tcx: 'a> {
    // A mapping from method call sites to traits that have that method.
    pub trait_map: ty::TraitMap,
    /// A vector of every trait accessible in the whole crate
    /// (i.e. including those from subcrates). This is used only for
    /// error reporting, and so is lazily initialised and generally
    /// shouldn't taint the common path (hence the RefCell).
    pub all_traits: RefCell<Option<check::method::AllTraitsVec>>,
    pub tcx: &'a ty::ctxt<'tcx>,
}

// Functions that write types into the node type table
fn write_ty_to_tcx<'tcx>(tcx: &ty::ctxt<'tcx>, node_id: ast::NodeId, ty: Ty<'tcx>) {
}

fn write_substs_to_tcx<'tcx>(tcx: &ty::ctxt<'tcx>,
                                 node_id: ast::NodeId,
                                 item_substs: ty::ItemSubsts<'tcx>) {
}

fn lookup_full_def(tcx: &ty::ctxt, sp: Span, id: ast::NodeId) -> def::Def {
}

fn require_same_types<'a, 'tcx, M>(tcx: &ty::ctxt<'tcx>,
                                   maybe_infcx: Option<&infer::InferCtxt<'a, 'tcx>>,
                                   t1_is_expected: bool,
                                   span: Span,
                                   t1: Ty<'tcx>,
                                   t2: Ty<'tcx>,
                                   msg: M)
                                   -> bool where
    M: FnOnce() -> String,
{
}

fn check_main_fn_ty(ccx: &CrateCtxt,
                    main_id: ast::NodeId,
                    main_span: Span) {
}

fn check_start_fn_ty(ccx: &CrateCtxt,
                     start_id: ast::NodeId,
                     start_span: Span) {
}

fn check_for_entry_fn(ccx: &CrateCtxt) {
}

pub fn check_crate(tcx: &ty::ctxt, trait_map: ty::TraitMap) {
}

#[cfg(stage0)]
__build_diagnostic_array! { DIAGNOSTICS }
#[cfg(not(stage0))]
__build_diagnostic_array! { librustc_typeck, DIAGNOSTICS }

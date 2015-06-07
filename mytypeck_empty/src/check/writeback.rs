// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Type resolution: the phase that finds all the types in the AST with
// unresolved type variables and replaces "ty_var" types with their
// substitutions.
use self::ResolveReason::*;

use astconv::AstConv;
use check::FnCtxt;
use middle::pat_util;
use middle::ty::{self, Ty, MethodCall, MethodCallee};
use middle::ty_fold::{TypeFolder,TypeFoldable};
use middle::infer;
use write_substs_to_tcx;
use write_ty_to_tcx;
use util::ppaux::Repr;

use std::cell::Cell;

use syntax::ast;
use syntax::ast_util;
use syntax::codemap::{DUMMY_SP, Span};
use syntax::print::pprust::pat_to_string;
use syntax::visit;
use syntax::visit::Visitor;

///////////////////////////////////////////////////////////////////////////
// Entry point functions

pub fn resolve_type_vars_in_expr(fcx: &FnCtxt, e: &ast::Expr) {
}

pub fn resolve_type_vars_in_fn(fcx: &FnCtxt,
                               decl: &ast::FnDecl,
                               blk: &ast::Block) {
}

///////////////////////////////////////////////////////////////////////////
// The Writerback context. This visitor walks the AST, checking the
// fn-specific tables to find references to types or regions. It
// resolves those regions to remove inference variables and writes the
// final result back into the master tables in the tcx. Here and
// there, it applies a few ad-hoc checks that were not convenient to
// do elsewhere.

struct WritebackCx<'cx, 'tcx: 'cx> {
    fcx: &'cx FnCtxt<'cx, 'tcx>,
}

impl<'cx, 'tcx> WritebackCx<'cx, 'tcx> {
    fn new(fcx: &'cx FnCtxt<'cx, 'tcx>) -> WritebackCx<'cx, 'tcx> {
    }

    fn tcx(&self) -> &'cx ty::ctxt<'tcx> {
    }

    // Hacky hack: During type-checking, we treat *all* operators
    // as potentially overloaded. But then, during writeback, if
    // we observe that something like `a+b` is (known to be)
    // operating on scalars, we clear the overload.
    fn fix_scalar_binary_expr(&mut self, e: &ast::Expr) {
    }
}

///////////////////////////////////////////////////////////////////////////
// Impl of Visitor for Resolver
//
// This is the master code which walks the AST. It delegates most of
// the heavy lifting to the generic visit and resolve functions
// below. In general, a function is made into a `visitor` if it must
// traffic in node-ids or update tables in the type context etc.

impl<'cx, 'tcx, 'v> Visitor<'v> for WritebackCx<'cx, 'tcx> {
    fn visit_item(&mut self, _: &ast::Item) {
        // Ignore items
    }

    fn visit_stmt(&mut self, s: &ast::Stmt) {
    }

    fn visit_expr(&mut self, e: &ast::Expr) {
    }

    fn visit_block(&mut self, b: &ast::Block) {
    }

    fn visit_pat(&mut self, p: &ast::Pat) {
    }

    fn visit_local(&mut self, l: &ast::Local) {
    }

    fn visit_ty(&mut self, t: &ast::Ty) {
    }
}

impl<'cx, 'tcx> WritebackCx<'cx, 'tcx> {
    fn visit_upvar_borrow_map(&self) {
    }

    fn visit_closures(&self) {
    }

    fn visit_node_id(&self, reason: ResolveReason, id: ast::NodeId) {
    }

    fn visit_adjustments(&self, reason: ResolveReason, id: ast::NodeId) {
    }

    fn visit_method_map_entry(&self,
                              reason: ResolveReason,
                              method_call: MethodCall) {
    }

    fn resolve<T:TypeFoldable<'tcx>>(&self, t: &T, reason: ResolveReason) -> T {
    }
}

///////////////////////////////////////////////////////////////////////////
// Resolution reason.

#[derive(Copy, Clone)]
enum ResolveReason {
    ResolvingExpr(Span),
    ResolvingLocal(Span),
    ResolvingPattern(Span),
    ResolvingUpvar(ty::UpvarId),
    ResolvingClosure(ast::DefId),
}

impl ResolveReason {
    fn span(&self, tcx: &ty::ctxt) -> Span {
    }
}

///////////////////////////////////////////////////////////////////////////
// The Resolver. This is the type folding engine that detects
// unresolved types and so forth.

struct Resolver<'cx, 'tcx: 'cx> {
    tcx: &'cx ty::ctxt<'tcx>,
    infcx: &'cx infer::InferCtxt<'cx, 'tcx>,
    writeback_errors: &'cx Cell<bool>,
    reason: ResolveReason,
}

impl<'cx, 'tcx> Resolver<'cx, 'tcx> {
    fn new(fcx: &'cx FnCtxt<'cx, 'tcx>,
           reason: ResolveReason)
           -> Resolver<'cx, 'tcx>
    {
    }

    fn from_infcx(infcx: &'cx infer::InferCtxt<'cx, 'tcx>,
                  writeback_errors: &'cx Cell<bool>,
                  reason: ResolveReason)
                  -> Resolver<'cx, 'tcx>
    {
    }

    fn report_error(&self, e: infer::fixup_err) {
    }
}

impl<'cx, 'tcx> TypeFolder<'tcx> for Resolver<'cx, 'tcx> {
    fn tcx<'a>(&'a self) -> &'a ty::ctxt<'tcx> {
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
    }

    fn fold_region(&mut self, r: ty::Region) -> ty::Region {
    }
}

///////////////////////////////////////////////////////////////////////////
// During type check, we store promises with the result of trait
// lookup rather than the actual results (because the results are not
// necessarily available immediately). These routines unwind the
// promises. It is expected that we will have already reported any
// errors that may be encountered, so if the promises store an error,
// a dummy result is returned.

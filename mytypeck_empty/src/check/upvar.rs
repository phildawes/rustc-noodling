// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! ### Inferring borrow kinds for upvars
//!
//! Whenever there is a closure expression, we need to determine how each
//! upvar is used. We do this by initially assigning each upvar an
//! immutable "borrow kind" (see `ty::BorrowKind` for details) and then
//! "escalating" the kind as needed. The borrow kind proceeds according to
//! the following lattice:
//!
//!     ty::ImmBorrow -> ty::UniqueImmBorrow -> ty::MutBorrow
//!
//! So, for example, if we see an assignment `x = 5` to an upvar `x`, we
//! will promote its borrow kind to mutable borrow. If we see an `&mut x`
//! we'll do the same. Naturally, this applies not just to the upvar, but
//! to everything owned by `x`, so the result is the same for something
//! like `x.f = 5` and so on (presuming `x` is not a borrowed pointer to a
//! struct). These adjustments are performed in
//! `adjust_upvar_borrow_kind()` (you can trace backwards through the code
//! from there).
//!
//! The fact that we are inferring borrow kinds as we go results in a
//! semi-hacky interaction with mem-categorization. In particular,
//! mem-categorization will query the current borrow kind as it
//! categorizes, and we'll return the *current* value, but this may get
//! adjusted later. Therefore, in this module, we generally ignore the
//! borrow kind (and derived mutabilities) that are returned from
//! mem-categorization, since they may be inaccurate. (Another option
//! would be to use a unification scheme, where instead of returning a
//! concrete borrow kind like `ty::ImmBorrow`, we return a
//! `ty::InferBorrow(upvar_id)` or something like that, but this would
//! then mean that all later passes would have to check for these figments
//! and report an error, and it just seems like more mess in the end.)

use super::FnCtxt;

use middle::expr_use_visitor as euv;
use middle::mem_categorization as mc;
use middle::ty::{self};
use middle::infer::{InferCtxt, UpvarRegion};
use std::collections::HashSet;
use syntax::ast;
use syntax::ast_util;
use syntax::codemap::Span;
use syntax::visit::{self, Visitor};
use util::ppaux::Repr;

///////////////////////////////////////////////////////////////////////////
// PUBLIC ENTRY POINTS

pub fn closure_analyze_fn(fcx: &FnCtxt,
                          _id: ast::NodeId,
                          _decl: &ast::FnDecl,
                          body: &ast::Block)
{
}

///////////////////////////////////////////////////////////////////////////
// SEED BORROW KIND

struct SeedBorrowKind<'a,'tcx:'a> {
    fcx: &'a FnCtxt<'a,'tcx>,
    closures_with_inferred_kinds: HashSet<ast::NodeId>,
}

impl<'a, 'tcx, 'v> Visitor<'v> for SeedBorrowKind<'a, 'tcx> {
    fn visit_expr(&mut self, expr: &ast::Expr) {
    }

    fn visit_fn(&mut self,
                fn_kind: visit::FnKind<'v>,
                decl: &'v ast::FnDecl,
                block: &'v ast::Block,
                span: Span,
                _id: ast::NodeId)
    {
    }
}

impl<'a,'tcx> SeedBorrowKind<'a,'tcx> {
    fn new(fcx: &'a FnCtxt<'a,'tcx>) -> SeedBorrowKind<'a,'tcx> {
    }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
    }

    fn infcx(&self) -> &'a InferCtxt<'a,'tcx> {
    }

    fn check_closure(&mut self,
                     expr: &ast::Expr,
                     capture_clause: ast::CaptureClause,
                     _body: &ast::Block)
    {
    }
}

///////////////////////////////////////////////////////////////////////////
// ADJUST BORROW KIND

struct AdjustBorrowKind<'a,'tcx:'a> {
    fcx: &'a FnCtxt<'a,'tcx>,
    closures_with_inferred_kinds: &'a HashSet<ast::NodeId>,
}

impl<'a,'tcx> AdjustBorrowKind<'a,'tcx> {
    fn new(fcx: &'a FnCtxt<'a,'tcx>,
           closures_with_inferred_kinds: &'a HashSet<ast::NodeId>)
           -> AdjustBorrowKind<'a,'tcx> {
    }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
    }

    fn analyze_closure(&mut self, id: ast::NodeId, decl: &ast::FnDecl, body: &ast::Block) {
    }

    fn adjust_upvar_borrow_kind_for_consume(&self,
                                            cmt: mc::cmt<'tcx>,
                                            mode: euv::ConsumeMode)
    {
    }

    /// Indicates that `cmt` is being directly mutated (e.g., assigned
    /// to). If cmt contains any by-ref upvars, this implies that
    /// those upvars must be borrowed using an `&mut` borrow.
    fn adjust_upvar_borrow_kind_for_mut(&mut self, cmt: mc::cmt<'tcx>) {
    }

    fn adjust_upvar_borrow_kind_for_unique(&self, cmt: mc::cmt<'tcx>) {
    }

    fn try_adjust_upvar_deref(&self,
                              note: &mc::Note,
                              borrow_kind: ty::BorrowKind)
                              -> bool
    {
    }

    /// We infer the borrow_kind with which to borrow upvars in a stack closure. The borrow_kind
    /// basically follows a lattice of `imm < unique-imm < mut`, moving from left to right as needed
    /// (but never right to left). Here the argument `mutbl` is the borrow_kind that is required by
    /// some particular use.
    fn adjust_upvar_borrow_kind(&self,
                                upvar_id: ty::UpvarId,
                                upvar_capture: &mut ty::UpvarCapture,
                                kind: ty::BorrowKind) {
    }

    fn adjust_closure_kind(&self,
                           closure_id: ast::NodeId,
                           new_kind: ty::ClosureKind) {
    }
}

impl<'a, 'tcx, 'v> Visitor<'v> for AdjustBorrowKind<'a, 'tcx> {
    fn visit_fn(&mut self,
                fn_kind: visit::FnKind<'v>,
                decl: &'v ast::FnDecl,
                body: &'v ast::Block,
                span: Span,
                id: ast::NodeId)
    {
    }
}

impl<'a,'tcx> euv::Delegate<'tcx> for AdjustBorrowKind<'a,'tcx> {
    fn consume(&mut self,
               _consume_id: ast::NodeId,
               _consume_span: Span,
               cmt: mc::cmt<'tcx>,
               mode: euv::ConsumeMode)
    {
    }

    fn matched_pat(&mut self,
                   _matched_pat: &ast::Pat,
                   _cmt: mc::cmt<'tcx>,
                   _mode: euv::MatchMode)
    {}

    fn consume_pat(&mut self,
                   _consume_pat: &ast::Pat,
                   cmt: mc::cmt<'tcx>,
                   mode: euv::ConsumeMode)
    {
    }

    fn borrow(&mut self,
              borrow_id: ast::NodeId,
              _borrow_span: Span,
              cmt: mc::cmt<'tcx>,
              _loan_region: ty::Region,
              bk: ty::BorrowKind,
              _loan_cause: euv::LoanCause)
    {
    }

    fn decl_without_init(&mut self,
                         _id: ast::NodeId,
                         _span: Span)
    {}

    fn mutate(&mut self,
              _assignment_id: ast::NodeId,
              _assignment_span: Span,
              assignee_cmt: mc::cmt<'tcx>,
              _mode: euv::MutateMode)
    {
    }
}

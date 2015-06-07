// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Method lookup: the secret sauce of Rust. See `README.md`.

use astconv::AstConv;
use check::FnCtxt;
use middle::def;
use middle::privacy::{AllPublic, DependsOn, LastPrivate, LastMod};
use middle::subst;
use middle::traits;
use middle::ty::{self, AsPredicate, ToPolyTraitRef};
use middle::infer;
use util::ppaux::Repr;

use syntax::ast::DefId;
use syntax::ast;
use syntax::codemap::Span;

pub use self::MethodError::*;
pub use self::CandidateSource::*;

pub use self::suggest::{report_error, AllTraitsVec};

mod confirm;
mod probe;
mod suggest;

pub enum MethodError {
    // Did not find an applicable method, but we did find various
    // static methods that may apply, as well as a list of
    // not-in-scope traits which may work.
    NoMatch(Vec<CandidateSource>, Vec<ast::DefId>, probe::Mode),

    // Multiple methods might apply.
    Ambiguity(Vec<CandidateSource>),

    // Using a `Fn`/`FnMut`/etc method on a raw closure type before we have inferred its kind.
    ClosureAmbiguity(/* DefId of fn trait */ ast::DefId),
}

// A pared down enum describing just the places from which a method
// candidate can arise. Used for error reporting only.
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub enum CandidateSource {
    ImplSource(ast::DefId),
    TraitSource(/* trait id */ ast::DefId),
}

type ItemIndex = usize; // just for doc purposes

/// Determines whether the type `self_ty` supports a method name `method_name` or not.
pub fn exists<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                        span: Span,
                        method_name: ast::Name,
                        self_ty: ty::Ty<'tcx>,
                        call_expr_id: ast::NodeId)
                        -> bool
{
}

/// Performs method lookup. If lookup is successful, it will return the callee and store an
/// appropriate adjustment for the self-expr. In some cases it may report an error (e.g., invoking
/// the `drop` method).
///
/// # Arguments
///
/// Given a method call like `foo.bar::<T1,...Tn>(...)`:
///
/// * `fcx`:                   the surrounding `FnCtxt` (!)
/// * `span`:                  the span for the method call
/// * `method_name`:           the name of the method being called (`bar`)
/// * `self_ty`:               the (unadjusted) type of the self expression (`foo`)
/// * `supplied_method_types`: the explicit method type parameters, if any (`T1..Tn`)
/// * `self_expr`:             the self expression (`foo`)
pub fn lookup<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                        span: Span,
                        method_name: ast::Name,
                        self_ty: ty::Ty<'tcx>,
                        supplied_method_types: Vec<ty::Ty<'tcx>>,
                        call_expr: &'tcx ast::Expr,
                        self_expr: &'tcx ast::Expr)
                        -> Result<ty::MethodCallee<'tcx>, MethodError>
{
}

pub fn lookup_in_trait<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                 span: Span,
                                 self_expr: Option<&ast::Expr>,
                                 m_name: ast::Name,
                                 trait_def_id: DefId,
                                 self_ty: ty::Ty<'tcx>,
                                 opt_input_types: Option<Vec<ty::Ty<'tcx>>>)
                                 -> Option<ty::MethodCallee<'tcx>>
{
}

/// `lookup_in_trait_adjusted` is used for overloaded operators. It does a very narrow slice of
/// what the normal probe/confirm path does. In particular, it doesn't really do any probing: it
/// simply constructs an obligation for a particular trait with the given self-type and checks
/// whether that trait is implemented.
///
/// FIXME(#18741) -- It seems likely that we can consolidate some of this code with the other
/// method-lookup code. In particular, autoderef on index is basically identical to autoderef with
/// normal probes, except that the test also looks for built-in indexing. Also, the second half of
/// this method is basically the same as confirmation.
pub fn lookup_in_trait_adjusted<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                                          span: Span,
                                          self_expr: Option<&ast::Expr>,
                                          m_name: ast::Name,
                                          trait_def_id: DefId,
                                          autoderefs: usize,
                                          unsize: bool,
                                          self_ty: ty::Ty<'tcx>,
                                          opt_input_types: Option<Vec<ty::Ty<'tcx>>>)
                                          -> Option<ty::MethodCallee<'tcx>>
{
}

pub fn resolve_ufcs<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                              span: Span,
                              method_name: ast::Name,
                              self_ty: ty::Ty<'tcx>,
                              expr_id: ast::NodeId)
                              -> Result<(def::Def, LastPrivate), MethodError>
{
}


/// Find item with name `item_name` defined in `trait_def_id` and return it, along with its
/// index (or `None`, if no such item).
fn trait_item<'tcx>(tcx: &ty::ctxt<'tcx>,
                    trait_def_id: ast::DefId,
                    item_name: ast::Name)
                    -> Option<(usize, ty::ImplOrTraitItem<'tcx>)>
{
}

fn impl_item<'tcx>(tcx: &ty::ctxt<'tcx>,
                   impl_def_id: ast::DefId,
                   item_name: ast::Name)
                   -> Option<ty::ImplOrTraitItem<'tcx>>
{
}

// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use check::regionck::{self, Rcx};

use middle::infer;
use middle::region;
use middle::subst::{self, Subst};
use middle::ty::{self, Ty};
use util::ppaux::{Repr, UserString};

use syntax::ast;
use syntax::codemap::{self, Span};

/// check_drop_impl confirms that the Drop implementation identfied by
/// `drop_impl_did` is not any more specialized than the type it is
/// attached to (Issue #8142).
///
/// This means:
///
/// 1. The self type must be nominal (this is already checked during
///    coherence),
///
/// 2. The generic region/type parameters of the impl's self-type must
///    all be parameters of the Drop impl itself (i.e. no
///    specialization like `impl Drop for Foo<i32>`), and,
///
/// 3. Any bounds on the generic parameters must be reflected in the
///    struct/enum definition for the nominal type itself (i.e.
///    cannot do `struct S<T>; impl<T:Clone> Drop for S<T> { ... }`).
///
pub fn check_drop_impl(tcx: &ty::ctxt, drop_impl_did: ast::DefId) -> Result<(), ()> {
}

fn ensure_drop_params_and_item_params_correspond<'tcx>(
    tcx: &ty::ctxt<'tcx>,
    drop_impl_did: ast::DefId,
    drop_impl_generics: &ty::Generics<'tcx>,
    drop_impl_ty: &ty::Ty<'tcx>,
    self_type_did: ast::DefId) -> Result<(), ()>
{
}

/// Confirms that every predicate imposed by dtor_predicates is
/// implied by assuming the predicates attached to self_type_did.
fn ensure_drop_predicates_are_implied_by_item_defn<'tcx>(
    tcx: &ty::ctxt<'tcx>,
    drop_impl_did: ast::DefId,
    dtor_predicates: &ty::GenericPredicates<'tcx>,
    self_type_did: ast::DefId,
    self_to_impl_substs: &subst::Substs<'tcx>) -> Result<(), ()> {
}

/// check_safety_of_destructor_if_necessary confirms that the type
/// expression `typ` conforms to the "Drop Check Rule" from the Sound
/// Generic Drop (RFC 769).
///
/// ----
///
/// The Drop Check Rule is the following:
///
/// Let `v` be some value (either temporary or named) and 'a be some
/// lifetime (scope). If the type of `v` owns data of type `D`, where
///
///   (1.) `D` has a lifetime- or type-parametric Drop implementation, and
///   (2.) the structure of `D` can reach a reference of type `&'a _`, and
///   (3.) either:
///
///     (A.) the Drop impl for `D` instantiates `D` at 'a directly,
///          i.e. `D<'a>`, or,
///
///     (B.) the Drop impl for `D` has some type parameter with a
///          trait bound `T` where `T` is a trait that has at least
///          one method,
///
/// then 'a must strictly outlive the scope of v.
///
/// ----
///
/// This function is meant to by applied to the type for every
/// expression in the program.
pub fn check_safety_of_destructor_if_necessary<'a, 'tcx>(rcx: &mut Rcx<'a, 'tcx>,
                                                     typ: ty::Ty<'tcx>,
                                                     span: Span,
                                                     scope: region::CodeExtent) {
}

enum Error<'tcx> {
    Overflow(TypeContext, ty::Ty<'tcx>),
}

enum TypeContext {
    Root,
    EnumVariant {
        def_id: ast::DefId,
        variant: ast::Name,
        arg_index: usize,
    },
    Struct {
        def_id: ast::DefId,
        field: ast::Name,
    }
}

// The `depth` counts the number of calls to this function;
// the `xref_depth` counts the subset of such calls that go
// across a `Box<T>` or `PhantomData<T>`.
fn iterate_over_potentially_unsafe_regions_in_type<'a, 'tcx>(
    rcx: &mut Rcx<'a, 'tcx>,
    breadcrumbs: &mut Vec<Ty<'tcx>>,
    context: TypeContext,
    ty_root: ty::Ty<'tcx>,
    span: Span,
    scope: region::CodeExtent,
    depth: usize,
    xref_depth: usize) -> Result<(), Error<'tcx>>
{
}

enum DtorKind<'tcx> {
    // Type has an associated drop method with this def id
    KnownDropMethod(ast::DefId),

    // Type has no destructor (or its dtor is known to be pure
    // with respect to lifetimes), though its *substructure*
    // may carry a destructor.
    PureRecur,

    // Type may have impure destructor that is unknown;
    // e.g. `Box<Trait+'a>`
    Unknown(ty::ExistentialBounds<'tcx>),
}

fn has_dtor_of_interest<'tcx>(tcx: &ty::ctxt<'tcx>,
                              dtor_kind: DtorKind,
                              typ: ty::Ty<'tcx>,
                              span: Span) -> bool {
}

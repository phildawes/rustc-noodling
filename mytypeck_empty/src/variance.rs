// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This file infers the variance of type and lifetime parameters. The
//! algorithm is taken from Section 4 of the paper "Taming the Wildcards:
//! Combining Definition- and Use-Site Variance" published in PLDI'11 and
//! written by Altidor et al., and hereafter referred to as The Paper.
//!
//! This inference is explicitly designed *not* to consider the uses of
//! types within code. To determine the variance of type parameters
//! defined on type `X`, we only consider the definition of the type `X`
//! and the definitions of any types it references.
//!
//! We only infer variance for type parameters found on *data types*
//! like structs and enums. In these cases, there is fairly straightforward
//! explanation for what variance means. The variance of the type
//! or lifetime parameters defines whether `T<A>` is a subtype of `T<B>`
//! (resp. `T<'a>` and `T<'b>`) based on the relationship of `A` and `B`
//! (resp. `'a` and `'b`).
//!
//! We do not infer variance for type parameters found on traits, fns,
//! or impls. Variance on trait parameters can make indeed make sense
//! (and we used to compute it) but it is actually rather subtle in
//! meaning and not that useful in practice, so we removed it. See the
//! addendum for some details. Variances on fn/impl parameters, otoh,
//! doesn't make sense because these parameters are instantiated and
//! then forgotten, they don't persist in types or compiled
//! byproducts.
//!
//! ### The algorithm
//!
//! The basic idea is quite straightforward. We iterate over the types
//! defined and, for each use of a type parameter X, accumulate a
//! constraint indicating that the variance of X must be valid for the
//! variance of that use site. We then iteratively refine the variance of
//! X until all constraints are met. There is *always* a sol'n, because at
//! the limit we can declare all type parameters to be invariant and all
//! constraints will be satisfied.
//!
//! As a simple example, consider:
//!
//!     enum Option<A> { Some(A), None }
//!     enum OptionalFn<B> { Some(|B|), None }
//!     enum OptionalMap<C> { Some(|C| -> C), None }
//!
//! Here, we will generate the constraints:
//!
//!     1. V(A) <= +
//!     2. V(B) <= -
//!     3. V(C) <= +
//!     4. V(C) <= -
//!
//! These indicate that (1) the variance of A must be at most covariant;
//! (2) the variance of B must be at most contravariant; and (3, 4) the
//! variance of C must be at most covariant *and* contravariant. All of these
//! results are based on a variance lattice defined as follows:
//!
//!       *      Top (bivariant)
//!    -     +
//!       o      Bottom (invariant)
//!
//! Based on this lattice, the solution V(A)=+, V(B)=-, V(C)=o is the
//! optimal solution. Note that there is always a naive solution which
//! just declares all variables to be invariant.
//!
//! You may be wondering why fixed-point iteration is required. The reason
//! is that the variance of a use site may itself be a function of the
//! variance of other type parameters. In full generality, our constraints
//! take the form:
//!
//!     V(X) <= Term
//!     Term := + | - | * | o | V(X) | Term x Term
//!
//! Here the notation V(X) indicates the variance of a type/region
//! parameter `X` with respect to its defining class. `Term x Term`
//! represents the "variance transform" as defined in the paper:
//!
//!   If the variance of a type variable `X` in type expression `E` is `V2`
//!   and the definition-site variance of the [corresponding] type parameter
//!   of a class `C` is `V1`, then the variance of `X` in the type expression
//!   `C<E>` is `V3 = V1.xform(V2)`.
//!
//! ### Constraints
//!
//! If I have a struct or enum with where clauses:
//!
//!     struct Foo<T:Bar> { ... }
//!
//! you might wonder whether the variance of `T` with respect to `Bar`
//! affects the variance `T` with respect to `Foo`. I claim no.  The
//! reason: assume that `T` is invariant w/r/t `Bar` but covariant w/r/t
//! `Foo`. And then we have a `Foo<X>` that is upcast to `Foo<Y>`, where
//! `X <: Y`. However, while `X : Bar`, `Y : Bar` does not hold.  In that
//! case, the upcast will be illegal, but not because of a variance
//! failure, but rather because the target type `Foo<Y>` is itself just
//! not well-formed. Basically we get to assume well-formedness of all
//! types involved before considering variance.
//!
//! ### Addendum: Variance on traits
//!
//! As mentioned above, we used to permit variance on traits. This was
//! computed based on the appearance of trait type parameters in
//! method signatures and was used to represent the compatibility of
//! vtables in trait objects (and also "virtual" vtables or dictionary
//! in trait bounds). One complication was that variance for
//! associated types is less obvious, since they can be projected out
//! and put to myriad uses, so it's not clear when it is safe to allow
//! `X<A>::Bar` to vary (or indeed just what that means). Moreover (as
//! covered below) all inputs on any trait with an associated type had
//! to be invariant, limiting the applicability. Finally, the
//! annotations (`MarkerTrait`, `PhantomFn`) needed to ensure that all
//! trait type parameters had a variance were confusing and annoying
//! for little benefit.
//!
//! Just for historical reference,I am going to preserve some text indicating
//! how one could interpret variance and trait matching.
//!
//! #### Variance and object types
//!
//! Just as with structs and enums, we can decide the subtyping
//! relationship between two object types `&Trait<A>` and `&Trait<B>`
//! based on the relationship of `A` and `B`. Note that for object
//! types we ignore the `Self` type parameter -- it is unknown, and
//! the nature of dynamic dispatch ensures that we will always call a
//! function that is expected the appropriate `Self` type. However, we
//! must be careful with the other type parameters, or else we could
//! end up calling a function that is expecting one type but provided
//! another.
//!
//! To see what I mean, consider a trait like so:
//!
//!     trait ConvertTo<A> {
//!         fn convertTo(&self) -> A;
//!     }
//!
//! Intuitively, If we had one object `O=&ConvertTo<Object>` and another
//! `S=&ConvertTo<String>`, then `S <: O` because `String <: Object`
//! (presuming Java-like "string" and "object" types, my go to examples
//! for subtyping). The actual algorithm would be to compare the
//! (explicit) type parameters pairwise respecting their variance: here,
//! the type parameter A is covariant (it appears only in a return
//! position), and hence we require that `String <: Object`.
//!
//! You'll note though that we did not consider the binding for the
//! (implicit) `Self` type parameter: in fact, it is unknown, so that's
//! good. The reason we can ignore that parameter is precisely because we
//! don't need to know its value until a call occurs, and at that time (as
//! you said) the dynamic nature of virtual dispatch means the code we run
//! will be correct for whatever value `Self` happens to be bound to for
//! the particular object whose method we called. `Self` is thus different
//! from `A`, because the caller requires that `A` be known in order to
//! know the return type of the method `convertTo()`. (As an aside, we
//! have rules preventing methods where `Self` appears outside of the
//! receiver position from being called via an object.)
//!
//! #### Trait variance and vtable resolution
//!
//! But traits aren't only used with objects. They're also used when
//! deciding whether a given impl satisfies a given trait bound. To set the
//! scene here, imagine I had a function:
//!
//!     fn convertAll<A,T:ConvertTo<A>>(v: &[T]) {
//!         ...
//!     }
//!
//! Now imagine that I have an implementation of `ConvertTo` for `Object`:
//!
//!     impl ConvertTo<int> for Object { ... }
//!
//! And I want to call `convertAll` on an array of strings. Suppose
//! further that for whatever reason I specifically supply the value of
//! `String` for the type parameter `T`:
//!
//!     let mut vector = vec!["string", ...];
//!     convertAll::<int, String>(vector);
//!
//! Is this legal? To put another way, can we apply the `impl` for
//! `Object` to the type `String`? The answer is yes, but to see why
//! we have to expand out what will happen:
//!
//! - `convertAll` will create a pointer to one of the entries in the
//!   vector, which will have type `&String`
//! - It will then call the impl of `convertTo()` that is intended
//!   for use with objects. This has the type:
//!
//!       fn(self: &Object) -> int
//!
//!   It is ok to provide a value for `self` of type `&String` because
//!   `&String <: &Object`.
//!
//! OK, so intuitively we want this to be legal, so let's bring this back
//! to variance and see whether we are computing the correct result. We
//! must first figure out how to phrase the question "is an impl for
//! `Object,int` usable where an impl for `String,int` is expected?"
//!
//! Maybe it's helpful to think of a dictionary-passing implementation of
//! type classes. In that case, `convertAll()` takes an implicit parameter
//! representing the impl. In short, we *have* an impl of type:
//!
//!     V_O = ConvertTo<int> for Object
//!
//! and the function prototype expects an impl of type:
//!
//!     V_S = ConvertTo<int> for String
//!
//! As with any argument, this is legal if the type of the value given
//! (`V_O`) is a subtype of the type expected (`V_S`). So is `V_O <: V_S`?
//! The answer will depend on the variance of the various parameters. In
//! this case, because the `Self` parameter is contravariant and `A` is
//! covariant, it means that:
//!
//!     V_O <: V_S iff
//!         int <: int
//!         String <: Object
//!
//! These conditions are satisfied and so we are happy.
//!
//! #### Variance and associated types
//!
//! Traits with associated types -- or at minimum projection
//! expressions -- must be invariant with respect to all of their
//! inputs. To see why this makes sense, consider what subtyping for a
//! trait reference means:
//!
//!    <T as Trait> <: <U as Trait>
//!
//! means that if I know that `T as Trait`, I also know that `U as
//! Trait`. Moreover, if you think of it as dictionary passing style,
//! it means that a dictionary for `<T as Trait>` is safe to use where
//! a dictionary for `<U as Trait>` is expected.
//!
//! The problem is that when you can project types out from `<T as
//! Trait>`, the relationship to types projected out of `<U as Trait>`
//! is completely unknown unless `T==U` (see #21726 for more
//! details). Making `Trait` invariant ensures that this is true.
//!
//! Another related reason is that if we didn't make traits with
//! associated types invariant, then projection is no longer a
//! function with a single result. Consider:
//!
//! ```
//! trait Identity { type Out; fn foo(&self); }
//! impl<T> Identity for T { type Out = T; ... }
//! ```
//!
//! Now if I have `<&'static () as Identity>::Out`, this can be
//! validly derived as `&'a ()` for any `'a`:
//!
//!    <&'a () as Identity> <: <&'static () as Identity>
//!    if &'static () < : &'a ()   -- Identity is contravariant in Self
//!    if 'static : 'a             -- Subtyping rules for relations
//!
//! This change otoh means that `<'static () as Identity>::Out` is
//! always `&'static ()` (which might then be upcast to `'a ()`,
//! separately). This was helpful in solving #21750.

use self::VarianceTerm::*;
use self::ParamKind::*;

use arena;
use arena::TypedArena;
use middle::resolve_lifetime as rl;
use middle::subst;
use middle::subst::{ParamSpace, FnSpace, TypeSpace, SelfSpace, VecPerParamSpace};
use middle::ty::{self, Ty};
use std::fmt;
use std::rc::Rc;
use syntax::ast;
use syntax::ast_map;
use syntax::ast_util;
use syntax::visit;
use syntax::visit::Visitor;
use util::nodemap::NodeMap;
use util::ppaux::Repr;

pub fn infer_variance(tcx: &ty::ctxt) {
    let krate = tcx.map.krate();
    let mut arena = arena::TypedArena::new();
    let terms_cx = determine_parameters_to_be_inferred(tcx, &mut arena, krate);
    let constraints_cx = add_constraints_from_crate(terms_cx, krate);
    solve_constraints(constraints_cx);
    tcx.variance_computed.set(true);
}

// Representing terms
//
// Terms are structured as a straightforward tree. Rather than rely on
// GC, we allocate terms out of a bounded arena (the lifetime of this
// arena is the lifetime 'a that is threaded around).
//
// We assign a unique index to each type/region parameter whose variance
// is to be inferred. We refer to such variables as "inferreds". An
// `InferredIndex` is a newtype'd int representing the index of such
// a variable.

type VarianceTermPtr<'a> = &'a VarianceTerm<'a>;

#[derive(Copy, Clone, Debug)]
struct InferredIndex(usize);

#[derive(Copy, Clone)]
enum VarianceTerm<'a> {
    ConstantTerm(ty::Variance),
    TransformTerm(VarianceTermPtr<'a>, VarianceTermPtr<'a>),
    InferredTerm(InferredIndex),
}

impl<'a> fmt::Debug for VarianceTerm<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    }
}

// The first pass over the crate simply builds up the set of inferreds.

struct TermsContext<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    arena: &'a TypedArena<VarianceTerm<'a>>,

    empty_variances: Rc<ty::ItemVariances>,

    // For marker types, UnsafeCell, and other lang items where
    // variance is hardcoded, records the item-id and the hardcoded
    // variance.
    lang_items: Vec<(ast::NodeId, Vec<ty::Variance>)>,

    // Maps from the node id of a type/generic parameter to the
    // corresponding inferred index.
    inferred_map: NodeMap<InferredIndex>,

    // Maps from an InferredIndex to the info for that variable.
    inferred_infos: Vec<InferredInfo<'a>> ,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum ParamKind {
    TypeParam,
    RegionParam,
}

struct InferredInfo<'a> {
    item_id: ast::NodeId,
    kind: ParamKind,
    space: ParamSpace,
    index: usize,
    param_id: ast::NodeId,
    term: VarianceTermPtr<'a>,

    // Initial value to use for this parameter when inferring
    // variance. For most parameters, this is Bivariant. But for lang
    // items and input type parameters on traits, it is different.
    initial_variance: ty::Variance,
}

fn determine_parameters_to_be_inferred<'a, 'tcx>(tcx: &'a ty::ctxt<'tcx>,
                                                 arena: &'a mut TypedArena<VarianceTerm<'a>>,
                                                 krate: &ast::Crate)
                                                 -> TermsContext<'a, 'tcx> {
}

fn lang_items(tcx: &ty::ctxt) -> Vec<(ast::NodeId,Vec<ty::Variance>)> {
}

impl<'a, 'tcx> TermsContext<'a, 'tcx> {
    fn add_inferreds_for_item(&mut self,
                              item_id: ast::NodeId,
                              has_self: bool,
                              generics: &ast::Generics)
    {
    }

    fn add_inferred(&mut self,
                    item_id: ast::NodeId,
                    kind: ParamKind,
                    space: ParamSpace,
                    index: usize,
                    param_id: ast::NodeId) {
    }

    fn pick_initial_variance(&self,
                             item_id: ast::NodeId,
                             space: ParamSpace,
                             index: usize)
                             -> ty::Variance
    {
    }

    fn num_inferred(&self) -> usize {
    }
}

impl<'a, 'tcx, 'v> Visitor<'v> for TermsContext<'a, 'tcx> {
    fn visit_item(&mut self, item: &ast::Item) {
    }
}

// Constraint construction and representation
//
// The second pass over the AST determines the set of constraints.
// We walk the set of items and, for each member, generate new constraints.

struct ConstraintContext<'a, 'tcx: 'a> {
    terms_cx: TermsContext<'a, 'tcx>,

    // These are pointers to common `ConstantTerm` instances
    covariant: VarianceTermPtr<'a>,
    contravariant: VarianceTermPtr<'a>,
    invariant: VarianceTermPtr<'a>,
    bivariant: VarianceTermPtr<'a>,

    constraints: Vec<Constraint<'a>> ,
}

/// Declares that the variable `decl_id` appears in a location with
/// variance `variance`.
#[derive(Copy, Clone)]
struct Constraint<'a> {
    inferred: InferredIndex,
    variance: &'a VarianceTerm<'a>,
}

fn add_constraints_from_crate<'a, 'tcx>(terms_cx: TermsContext<'a, 'tcx>,
                                        krate: &ast::Crate)
                                        -> ConstraintContext<'a, 'tcx>
{
}

impl<'a, 'tcx, 'v> Visitor<'v> for ConstraintContext<'a, 'tcx> {
    fn visit_item(&mut self, item: &ast::Item) {
    }
}

/// Is `param_id` a lifetime according to `map`?
fn is_lifetime(map: &ast_map::Map, param_id: ast::NodeId) -> bool {
}

impl<'a, 'tcx> ConstraintContext<'a, 'tcx> {
    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
    }

    fn inferred_index(&self, param_id: ast::NodeId) -> InferredIndex {
    }

    fn find_binding_for_lifetime(&self, param_id: ast::NodeId) -> ast::NodeId {
    }

    /// Is `param_id` a type parameter for which we infer variance?
    fn is_to_be_inferred(&self, param_id: ast::NodeId) -> bool {
    }

    /// Returns a variance term representing the declared variance of the type/region parameter
    /// with the given id.
    fn declared_variance(&self,
                         param_def_id: ast::DefId,
                         item_def_id: ast::DefId,
                         kind: ParamKind,
                         space: ParamSpace,
                         index: usize)
                         -> VarianceTermPtr<'a> {
    }

    fn add_constraint(&mut self,
                      InferredIndex(index): InferredIndex,
                      variance: VarianceTermPtr<'a>) {
    }

    fn contravariant(&mut self,
                     variance: VarianceTermPtr<'a>)
                     -> VarianceTermPtr<'a> {
    }

    fn invariant(&mut self,
                 variance: VarianceTermPtr<'a>)
                 -> VarianceTermPtr<'a> {
    }

    fn constant_term(&self, v: ty::Variance) -> VarianceTermPtr<'a> {
    }

    fn xform(&mut self,
             v1: VarianceTermPtr<'a>,
             v2: VarianceTermPtr<'a>)
             -> VarianceTermPtr<'a> {
    }

    fn add_constraints_from_trait_ref(&mut self,
                                      generics: &ty::Generics<'tcx>,
                                      trait_ref: ty::TraitRef<'tcx>,
                                      variance: VarianceTermPtr<'a>) {
    }

    /// Adds constraints appropriate for an instance of `ty` appearing
    /// in a context with the generics defined in `generics` and
    /// ambient variance `variance`
    fn add_constraints_from_ty(&mut self,
                               generics: &ty::Generics<'tcx>,
                               ty: Ty<'tcx>,
                               variance: VarianceTermPtr<'a>) {
    }


    /// Adds constraints appropriate for a nominal type (enum, struct,
    /// object, etc) appearing in a context with ambient variance `variance`
    fn add_constraints_from_substs(&mut self,
                                   generics: &ty::Generics<'tcx>,
                                   def_id: ast::DefId,
                                   type_param_defs: &[ty::TypeParameterDef<'tcx>],
                                   region_param_defs: &[ty::RegionParameterDef],
                                   substs: &subst::Substs<'tcx>,
                                   variance: VarianceTermPtr<'a>) {
    }

    /// Adds constraints appropriate for a function with signature
    /// `sig` appearing in a context with ambient variance `variance`
    fn add_constraints_from_sig(&mut self,
                                generics: &ty::Generics<'tcx>,
                                sig: &ty::PolyFnSig<'tcx>,
                                variance: VarianceTermPtr<'a>) {
    }

    /// Adds constraints appropriate for a region appearing in a
    /// context with ambient variance `variance`
    fn add_constraints_from_region(&mut self,
                                   _generics: &ty::Generics<'tcx>,
                                   region: ty::Region,
                                   variance: VarianceTermPtr<'a>) {
    }

    /// Adds constraints appropriate for a mutability-type pair
    /// appearing in a context with ambient variance `variance`
    fn add_constraints_from_mt(&mut self,
                               generics: &ty::Generics<'tcx>,
                               mt: &ty::mt<'tcx>,
                               variance: VarianceTermPtr<'a>) {
    }
}

// Constraint solving
//
// The final phase iterates over the constraints, refining the variance
// for each inferred until a fixed point is reached. This will be the
// optimal solution to the constraints. The final variance for each
// inferred is then written into the `variance_map` in the tcx.

struct SolveContext<'a, 'tcx: 'a> {
    terms_cx: TermsContext<'a, 'tcx>,
    constraints: Vec<Constraint<'a>> ,

    // Maps from an InferredIndex to the inferred value for that variable.
    solutions: Vec<ty::Variance> }

fn solve_constraints(constraints_cx: ConstraintContext) {
}

impl<'a, 'tcx> SolveContext<'a, 'tcx> {
    fn solve(&mut self) {
    }

    fn write(&self) {
    }

    fn evaluate(&self, term: VarianceTermPtr<'a>) -> ty::Variance {
    }
}

// Miscellany transformations on variance

trait Xform {
    fn xform(self, v: Self) -> Self;
}

impl Xform for ty::Variance {
    fn xform(self, v: ty::Variance) -> ty::Variance {
    }
}

fn glb(v1: ty::Variance, v2: ty::Variance) -> ty::Variance {
}

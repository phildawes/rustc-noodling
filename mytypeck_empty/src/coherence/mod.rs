// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Coherence phase
//
// The job of the coherence phase of typechecking is to ensure that
// each trait has at most one implementation for each type. This is
// done by the orphan and overlap modules. Then we build up various
// mappings. That mapping code resides here.


use middle::lang_items::UnsizeTraitLangItem;
use middle::subst::{self, Subst};
use middle::traits;
use middle::ty::RegionEscape;
use middle::ty::{ImplContainer, ImplOrTraitItemId, ConstTraitItemId};
use middle::ty::{MethodTraitItemId, TypeTraitItemId, ParameterEnvironment};
use middle::ty::{Ty, ty_bool, ty_char, ty_enum, ty_err};
use middle::ty::{ty_param, TypeScheme, ty_ptr};
use middle::ty::{ty_rptr, ty_struct, ty_trait, ty_tup};
use middle::ty::{ty_str, ty_vec, ty_float, ty_infer, ty_int};
use middle::ty::{ty_uint, ty_closure, ty_uniq, ty_bare_fn};
use middle::ty::ty_projection;
use middle::ty;
use middle::free_region::FreeRegionMap;
use CrateCtxt;
use middle::infer::{self, InferCtxt, new_infer_ctxt};
use std::cell::RefCell;
use std::rc::Rc;
use syntax::ast::{Crate, DefId};
use syntax::ast::{Item, ItemImpl};
use syntax::ast::{LOCAL_CRATE};
use syntax::ast;
use syntax::ast_map::NodeItem;
use syntax::ast_map;
use syntax::ast_util::local_def;
use syntax::codemap::Span;
use syntax::parse::token;
use syntax::visit;
use util::nodemap::{DefIdMap, FnvHashMap};
use util::ppaux::Repr;

mod orphan;
mod overlap;
mod unsafety;

// Returns the def ID of the base type, if there is one.
fn get_base_type_def_id<'a, 'tcx>(inference_context: &InferCtxt<'a, 'tcx>,
                                  span: Span,
                                  ty: Ty<'tcx>)
                                  -> Option<DefId> {
}

pub struct CoherenceChecker<'a, 'tcx: 'a> {
    pub crate_context: &'a CrateCtxt<'a, 'tcx>,
    pub inference_context: InferCtxt<'a, 'tcx>,
    pub inherent_impls: RefCell<DefIdMap<Rc<RefCell<Vec<ast::DefId>>>>>,
}

struct CoherenceCheckVisitor<'a, 'tcx: 'a> {
    cc: &'a CoherenceChecker<'a, 'tcx>
}

impl<'a, 'tcx, 'v> visit::Visitor<'v> for CoherenceCheckVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &Item) {
    }
}

impl<'a, 'tcx> CoherenceChecker<'a, 'tcx> {
    pub fn check(&self, krate: &Crate) {
    }

    fn check_implementation(&self, item: &Item) {
    }

    // Creates default method IDs and performs type substitutions for an impl
    // and trait pair. Then, for each provided method in the trait, inserts a
    // `ProvidedMethodInfo` instance into the `provided_method_sources` map.
    fn instantiate_default_methods(
            &self,
            impl_id: DefId,
            trait_ref: &ty::TraitRef<'tcx>,
            all_impl_items: &mut Vec<ImplOrTraitItemId>) {
    }

    fn add_inherent_impl(&self, base_def_id: DefId, impl_def_id: DefId) {
    }

    fn add_trait_impl(&self, impl_trait_ref: ty::TraitRef<'tcx>, impl_def_id: DefId) {
    }

    // Converts an implementation in the AST to a vector of items.
    fn create_impl_from_item(&self, item: &Item) -> Vec<ImplOrTraitItemId> {
    }

    //
    // Destructors
    //

    fn populate_destructor_table(&self) {
    }

    /// Ensures that implementations of the built-in trait `Copy` are legal.
    fn check_implementations_of_copy(&self) {
    }

    /// Process implementations of the built-in trait `CoerceUnsized`.
    fn check_implementations_of_coerce_unsized(&self) {
    }
}

fn enforce_trait_manually_implementable(tcx: &ty::ctxt, sp: Span, trait_def_id: ast::DefId) {
}

fn subst_receiver_types_in_method_ty<'tcx>(tcx: &ty::ctxt<'tcx>,
                                           impl_id: ast::DefId,
                                           impl_type_scheme: &ty::TypeScheme<'tcx>,
                                           trait_ref: &ty::TraitRef<'tcx>,
                                           new_def_id: ast::DefId,
                                           method: &ty::Method<'tcx>,
                                           provided_source: Option<ast::DefId>)
                                           -> ty::Method<'tcx>
{
}

pub fn check_coherence(crate_context: &CrateCtxt) {
}

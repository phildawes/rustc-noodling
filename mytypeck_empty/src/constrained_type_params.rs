// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::subst;
use middle::ty::{self, Ty};

use std::collections::HashSet;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Parameter {
    Type(ty::ParamTy),
    Region(ty::EarlyBoundRegion),
}

pub fn parameters_for_type<'tcx>(ty: Ty<'tcx>) -> Vec<Parameter> {
}

pub fn parameters_for_trait_ref<'tcx>(trait_ref: &ty::TraitRef<'tcx>) -> Vec<Parameter> {
}

fn parameters_for_type_shallow<'tcx>(ty: Ty<'tcx>) -> Vec<Parameter> {
}

fn parameters_for_regions_in_substs(substs: &subst::Substs) -> Vec<Parameter> {
}

fn parameters_for_region(region: &ty::Region) -> Option<Parameter> {
}

pub fn identify_constrained_type_params<'tcx>(_tcx: &ty::ctxt<'tcx>,
                                              predicates: &[ty::Predicate<'tcx>],
                                              impl_trait_ref: Option<ty::TraitRef<'tcx>>,
                                              input_parameters: &mut HashSet<Parameter>)
{
}

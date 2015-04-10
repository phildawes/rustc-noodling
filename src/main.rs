#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_driver;
extern crate rustc_typeck;
extern crate rustc_resolve;
extern crate syntax;
extern crate time;

use std::path::{Path};

use rustc::session::{self,config};

use syntax::diagnostic;
use syntax::diagnostic::Emitter;
use rustc_driver::driver;
// use rustc_lint;
use rustc_resolve as resolve;
use rustc_typeck::middle::lang_items;
use rustc_typeck::middle::region;
use rustc_typeck::middle::resolve_lifetime;
use rustc_typeck::middle::stability;
// use rustc_typeck::middle::subst;
// use rustc_typeck::middle::subst::Subst;
use rustc_typeck::middle::ty;
// use rustc_typeck::middle::ty_relate::TypeRelation;
// use rustc_typeck::middle::infer;
// use rustc_typeck::middle::infer::lub::Lub;
// use rustc_typeck::middle::infer::glb::Glb;
// use rustc_typeck::middle::infer::sub::Sub;
// use rustc_typeck::util::ppaux::{ty_to_string, Repr, UserString};
// use rustc::session::{self,config};
use syntax::{ast_map};
use syntax::codemap;
use syntax::codemap::{Span, CodeMap};
use syntax::diagnostic::{Level, RenderSpan};
// use syntax::parse::token;
use rustc::metadata::creader::CrateReader;

use std::io::Read;

// Stub error emitter
struct MyErrorEmitter;

impl Emitter for MyErrorEmitter {
    fn emit(&mut self,
            _cmsp: Option<(&codemap::CodeMap, Span)>,
            msg: &str,
            _: Option<&str>,
            lvl: Level)
    {
        println!("PHIL {:?} msg={}",lvl, msg);
        //remove_message(self, msg, lvl);
    }

    fn custom_emit(&mut self,
                   _cm: &codemap::CodeMap,
                   _sp: RenderSpan,
                   msg: &str,
                   lvl: Level)
    {
        println!("PHIL {:?} msg={}",lvl, msg);
    }
}

fn main() {

    let t0 = time::precise_time_s();

    let mut options =
        config::basic_options();

    let fpath = Path::new("/tmp/input.rs");

    let mut input = String::new();
    let mut f = std::fs::File::open(fpath).unwrap();
    f.read_to_string(&mut input);
    let input = config::Input::Str(input);
    // let input = config::Input::Str("
    // struct FooStruct;
    // fn fn2() -> FooStruct {}

    // fn myfn(apple: &FooStruct){ 
    //      let barge = fn2(); 
    // }".to_string());

    options.debugging_opts.verbose = true;
    options.unstable_features = config::UnstableFeatures::Default;
    let mut crate_types = Vec::new();
    crate_types.push(config::CrateType::CrateTypeExecutable);
    options.crate_types = crate_types;
    options.maybe_sysroot = Some(Path::new("/usr/local").to_path_buf());

    options.debugging_opts.verbose = true;
    let codemap =
        CodeMap::new();

    let emitter = Box::new(MyErrorEmitter);

    let diagnostic_handler =
        diagnostic::mk_handler(true, emitter);
    let span_diagnostic_handler =
        diagnostic::mk_span_handler(diagnostic_handler, codemap);


    let sess = session::build_session_(options, Some(fpath.to_path_buf()), span_diagnostic_handler);
    let krate_config = Vec::new();

    let krate = driver::phase_1_parse_input(&sess, krate_config, &input);
    let krate = driver::phase_2_configure_and_expand(&sess, krate, "a", None)
                    .expect("phase 2 aborted");


    let mut forest = ast_map::Forest::new(krate);
    let arenas = ty::CtxtArenas::new();
    let ast_map = driver::assign_node_ids_and_map(&sess, &mut forest);
    let krate = ast_map.krate();

    CrateReader::new(&sess).read_crates(krate);

    let lang_items = lang_items::collect_language_items(krate, &sess);
    let resolve::CrateMap {
        def_map,
        freevars,
        export_map,
        trait_map,
        ..
    } = resolve::resolve_crate(&sess, &ast_map, 
                               &lang_items, krate, resolve::MakeGlobMap::No);

    let t1 = time::precise_time_s();

    let named_region_map = resolve_lifetime::krate(&sess, krate, &def_map);
    let region_map = region::resolve_crate(&sess, krate);
    let tcx = ty::mk_ctxt(sess,
                          &arenas,
                          def_map,
                          named_region_map,
                          ast_map,
                          freevars,
                          region_map,
                          lang_items,
                          stability::Index::new(krate));
    
    rustc_typeck::check_crate(&tcx, trait_map);

    let t2 = time::precise_time_s();

    println!("time is {} {}", (t1-t0), (t2-t0));
    println!("PHIL node_types is {:?}\n",tcx.node_types());
    println!("PHIL def_map is {:?}\n",tcx.def_map);
    println!("PHIL krate is {:?}",krate);
}

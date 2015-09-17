#![feature(rustc_private)]

extern crate rustc;
extern crate syntax;
extern crate rustc_driver;
extern crate rustc_lint;
extern crate rustc_front;
extern crate rustc_resolve;

// PD: patched rustc_typeck to allow access to some elements. see mytypeck.patch
extern crate mytypeck;


use rustc::session::{self,config};
use rustc::metadata;
use std::path::{Path};
use syntax::feature_gate::UnstableFeatures;
use syntax::codemap;
use syntax::codemap::{Span, CodeMap};
use syntax::diagnostic::{self, Level, RenderSpan};
use syntax::diagnostic::Emitter;

use rustc_driver::driver;
use std::env;

use rustc_front::lowering::lower_crate;
use rustc::front::map as hir_map;
use mytypeck::middle::ty::{self};
use mytypeck::middle::lang_items;
use rustc_resolve as resolve;
use mytypeck::middle::resolve_lifetime;
use mytypeck::middle::region::{self};
use mytypeck::middle::stability;

use mytypeck::CrateCtxt;
use std::cell::RefCell;
use mytypeck::collect;
use mytypeck::check;
use mytypeck::coherence;
use rustc::plugin;

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


pub fn run_type_inference() {
    let emitter = Box::new(MyErrorEmitter);

    env::set_var("CFG_COMPILER_HOST_TRIPLE","x86_64-unknown-linux-gnu");

    let fname = std::env::args().nth(1).unwrap();

    println!("PHIL 0.1");
    let mut options =
        config::basic_options();

    let fpath = Path::new(&fname);

    println!("PHIL 0.2");
    options.debugging_opts.verbose = true;
    options.unstable_features = UnstableFeatures::Allow;

    let mut crate_types = Vec::new();
    crate_types.push(config::CrateType::CrateTypeExecutable);
    options.crate_types = crate_types;

    options.maybe_sysroot = Some(Path::new("/home/pld/.multirust/toolchains/nightly/").to_path_buf());

    println!("PHIL 0.3");
    let codemap =
        CodeMap::new();
    let diagnostic_handler =
        diagnostic::Handler::with_emitter(true, emitter);
    let span_diagnostic_handler =
        diagnostic::SpanHandler::new(diagnostic_handler, codemap);

    println!("PHIL 0.4");
    let sess = session::build_session_(options, None, span_diagnostic_handler);

    // rustc_lint::register_builtins(&mut sess.lint_store.borrow_mut(), Some(&sess));
    let krate_config = Vec::new();

    println!("PHIL 0.5");
    let input = config::Input::File(fpath.to_path_buf());
    let krate = driver::phase_1_parse_input(&sess, krate_config, &input);
    let krate = driver::phase_2_configure_and_expand(&sess, krate, "test", None)
                    .expect("phase 2 aborted");

    ///////// PD: Assign ids
    println!("PHIL 0.6");
    let krate = driver::assign_node_ids(&sess, krate);
    let mut hir_forest = hir_map::Forest::new(lower_crate(&krate));
    let arenas = ty::CtxtArenas::new();
    let ast_map = driver::make_map(&sess, &mut hir_forest);


    ///////// PD: phase 3 analysis passes
    println!("PHIL 0.7");
    let krate = ast_map.krate();

    metadata::creader::LocalCrateReader::new(&sess, &ast_map).read_crates(krate);

    println!("PHIL 1");
    let lang_items = lang_items::collect_language_items(krate, &sess);
    println!("PHIL 2");
    let m = resolve::resolve_crate(&sess, &ast_map, resolve::MakeGlobMap::No);

    let resolve::CrateMap { def_map, freevars, trait_map, .. } = m;

    syntax::ext::mtwt::clear_tables();

    println!("PHIL 3");
    let named_region_map = resolve_lifetime::krate(&sess, krate, &def_map);

    //mytypeck::middle::entry::find_entry_point(&sess, &ast_map);

    println!("PHIL 3.1");
    // PD: maybe don't need this
    sess.plugin_registrar_fn.set(
        plugin::build::find_plugin_registrar(sess.diagnostic(), krate));
    
    println!("PHIL 4");
    let region_map = region::resolve_crate(&sess, krate);

    // PD: maybe don't need this
    rustc::middle::check_loop::check_crate(&sess, krate);
    rustc::middle::check_static_recursion::check_crate(&sess, krate, &def_map, &ast_map);

    println!("PHIL 5");
    ty::ctxt::create_and_enter(sess,
       &arenas,
       def_map,
       named_region_map,
       ast_map,
       freevars,
       region_map,
       lang_items,
       stability::Index::new(krate),
       |tcx| {
           println!("PHIL 6.1");
           // passes are timed inside typeck

           let ccx = CrateCtxt {
               trait_map: trait_map,
               all_traits: RefCell::new(None),
               tcx: tcx
           };

           // mytypeck::check_crate(tcx, trait_map);
           collect::collect_item_types(tcx);
           println!("PHIL 6.1");
           //tcx.sess.abort_if_errors();
           println!("PHIL 6.1.1");
           mytypeck::variance::infer_variance(tcx);

           println!("PHIL 6.2");
           coherence::check_coherence(&ccx);
           println!("PHIL 6.2.2");
           check::check_wf_old(&ccx);
           println!("PHIL 6.2.3");
           check::check_item_types(&ccx);
           println!("PHIL 6.3");
           check::check_item_bodies(&ccx);
           println!("PHIL 7");
           check::check_drop_impls(&ccx);
           check::check_wf_new(&ccx);

           tcx.sess.abort_if_errors();
       });
    println!("PHIL 8");

}

fn main() {
    run_type_inference();
}

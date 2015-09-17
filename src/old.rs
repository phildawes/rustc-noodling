#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_driver;
extern crate mytypeck; // copy of rustc_typeck with some private fns made public
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
use mytypeck::middle::lang_items;
use mytypeck::middle::region;
use mytypeck::middle::resolve_lifetime;
use rustc::middle::stability;
use rustc::middle::ty;
use syntax::{ast_map, ast};
use syntax::codemap;
use syntax::codemap::{Span, CodeMap};
use syntax::diagnostic::{Level, RenderSpan};
use rustc::metadata::creader::CrateReader;
use rustc::middle::infer::new_infer_ctxt;
use rustc::util::nodemap::FnvHashMap;
use syntax::visit::{self, Visitor};
use rustc::util::ppaux;
use syntax::fold::{self,Folder};
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

use mytypeck::CrateCtxt;
use std::cell::RefCell;
use mytypeck::collect;
use mytypeck::variance;
use mytypeck::coherence;
//use mytypeck::check;
//use mytypeck::check_for_entry_fn;

struct Timer {
    t0: f64,
    tv: Vec<(&'static str, f64, f64)>,
}

impl Timer {
    fn new() -> Timer {
        let mut t = Timer{ t0: time::precise_time_s(), tv: Vec::new() };
        t.tv.push(("start", t.t0, 0.0));
        t
    }

    fn add(&mut self, s: &'static str) {
        let t = time::precise_time_s();
        let prev = self.tv.last().unwrap().1;
        self.tv.push((s,t,t-prev));
    }
}

fn create_session() -> session::Session {
    let mut options =
        config::basic_options();

    options.debugging_opts.verbose = true;
    options.unstable_features = config::UnstableFeatures::Default;
    let mut crate_types = Vec::new();
    crate_types.push(config::CrateType::CrateTypeExecutable);
    options.crate_types = crate_types;
    //options.maybe_sysroot = Some(Path::new("/usr/local").to_path_buf());
    options.maybe_sysroot = Some(Path::new("/home/pld/.multirust/toolchains/nightly/").to_path_buf());

    options.debugging_opts.verbose = true;
    let codemap = CodeMap::new();

    let emitter = Box::new(MyErrorEmitter);
    let diagnostic_handler =
        diagnostic::Handler::with_emitter(true, emitter);
    let span_diagnostic_handler =
        diagnostic::SpanHandler::new(diagnostic_handler, codemap);
    let sess = session::build_session_(options, None, span_diagnostic_handler);
    sess
}


fn try_modify_crate() {
    let src = "
use std::io::Read;
struct Foo;
fn myfn(){
}
";

    let krate_config = Vec::new();
    let input = config::Input::Str(src.to_string());

    let sess = create_session();

    // parse a the crate
    let krate = driver::phase_1_parse_input(&sess, krate_config, &input);

    let skeleton_krate = driver::phase_2_configure_and_expand(&sess, krate, "a", None)
                    .expect("phase 2 aborted");

    // cache the krate!
    let mut krate = skeleton_krate.clone();

    {
        // INSERT SOME AST!!
        let src="
fn bar() -> Foo {
    let i = 35;
    println!(\"hello\");
    Foo
}
";

        let src="
fn bar<T:Read>(v: Vec<T>) {
    let b = v.pop().unwrap();
    let buf: &mut [u8];
    b.read(buf);
}
";

        let mut parser = string_to_parser(&sess.parse_sess, src.to_string()).unwrap();
        let ffn = parser.parse_item().unwrap();

        struct TestFolder(syntax::ptr::P<syntax::ast::Item>);
        impl fold::Folder for TestFolder {
            fn fold_mod(&mut self, mut m: ast::Mod) -> ast::Mod {
                m.items.push(self.0.clone());
                m
            }
        }

        let mut f = TestFolder(ffn);
        krate = f.fold_crate(krate);
    }

    perform_second_phase(krate);  
}


fn perform_second_phase(krate: ast::Crate) {
    // try with a brand new session
    let sess = create_session();

    let mut krate = phase_2_configure_and_expand_without_std_inject(&sess, krate, "a", None)
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

    // The following is from typeck::check_crate(&ty_cx, trait_map);
    let ccx = CrateCtxt {
        trait_map: trait_map,
        all_traits: RefCell::new(None),
        tcx: &tcx
    };

    collect::collect_item_types(&tcx);


    variance::infer_variance(&tcx);


    // Can we do without coherence checking?

    // this is from     coherence::check_coherence(&ccx);
    coherence::CoherenceChecker {
        crate_context: &ccx,
        inference_context: new_infer_ctxt(ccx.tcx),
        inherent_impls: RefCell::new(FnvHashMap()),
    }.check(&ccx.tcx.map.krate());

    check_item_types(&ccx);
    
    print_expr_types(&tcx, krate);
}


// 'a is the lifetime of the ty::ctxt reference and the Crate reference
// 'tcx is the lifetime of the arena inside tcx
// the lifetime of the crate instance is not mentioned.

fn print_expr_types<'a, 'tcx>(tcx: &'a ty::ctxt<'tcx>, krate: &'a ast::Crate) {
    struct MyExprVisitor<'a, 'tcx: 'a>(&'a ty::ctxt<'tcx>, bool);

    impl<'a, 'tcx> visit::Visitor<'a> for MyExprVisitor<'a, 'tcx> {
        // fn visit_fn(&mut self, fk: visit::FnKind<'a>, 
        //             fd: &'a ast::FnDecl, 
        //             b: &'a ast::Block, 
        //             s: Span, _: ast::NodeId) {

        //     match fk {
        //         visit::FnKind::FkItemFn(ident, _, _, _, _, _) => {
        //             if ident.as_str() == "check_bounds_are_used" {
        //                 self.1 = true;
        //                 println!("PHIL found fn");
        //                 visit::walk_fn(self, fk, fd, b, s);
        //                 println!("PHIL finished fn");
        //                 self.1 = false;
        //             }
        //         },
        //         _ => {}

        //     }
        // }

        fn visit_item(&mut self, i: &'a ast::Item) {
            if i.ident.as_str() == "check_bounds_are_used" {
                self.1 = true;
                visit::walk_item(self, i);
                self.1 = false;
            } else {
                visit::walk_item(self, i);
            }
        }
        fn visit_expr(&mut self, ex: &'a ast::Expr) {
            if self.1 {
                let ty_ = ty::expr_ty(self.0, ex);

                let s = ppaux::ty_to_string(self.0, ty_);
                println!("PHIL s is {}",s);
                visit::walk_expr(self, ex);
            }
        }
    }

    let mut v = MyExprVisitor(tcx, false);
    visit::walk_crate(&mut v, krate);
    
}

use syntax::parse::parser::Parser;
use syntax::parse::{lexer, ParseSess, token};

pub fn string_to_parser<'a>(ps: &'a ParseSess, source_str: String) -> Option<Parser<'a>> {
    let fm = ps.codemap().new_filemap("bogofile".to_string(), source_str);
    let srdr = lexer::StringReader::new(&ps.span_diagnostic, fm);
    let p = Parser::new(ps, Vec::new(), Box::new(srdr));
    Some(p)
}


pub struct MyFileLoader;
use std::io;
use std::io::Read;

impl codemap::FileLoader for MyFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        std::fs::metadata(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        println!("PHIL reading file: {:?}",path);
        let mut src = String::new();
        try!(try!(std::fs::File::open(path)).read_to_string(&mut src));
        Ok(src)
    }
}


pub fn try_resolve_expr_types() {
    //let mut tv = Vec::new();
    let mut tv = Timer::new();
    let fname = std::env::args().nth(1).unwrap();

    let mut options =
        config::basic_options();

    let fpath = Path::new(&fname);
    let input = config::Input::File(fpath.to_path_buf());

    options.debugging_opts.verbose = true;
    options.unstable_features = config::UnstableFeatures::Default;
    let mut crate_types = Vec::new();
    crate_types.push(config::CrateType::CrateTypeExecutable);
    options.crate_types = crate_types;
    //options.maybe_sysroot = Some(Path::new("/usr/local").to_path_buf());
    options.maybe_sysroot = Some(Path::new("/home/pld/.multirust/toolchains/nightly/").to_path_buf());

    options.debugging_opts.verbose = true;
    //let codemap = CodeMap::new();
    let codemap = CodeMap::with_file_loader(Box::new(MyFileLoader));

    let emitter = Box::new(MyErrorEmitter);

    let diagnostic_handler =
        diagnostic::Handler::with_emitter(true, emitter);
    let span_diagnostic_handler =
        diagnostic::SpanHandler::new(diagnostic_handler, codemap);

    let sess = session::build_session_(options, Some(fpath.to_path_buf()), span_diagnostic_handler);
    let krate_config = Vec::new();

    tv.add("setup");

    // parse a the crate
    let krate = driver::phase_1_parse_input(&sess, krate_config, &input);

    tv.add("parse");

    let krate = driver::phase_2_configure_and_expand(&sess, krate, "a", None)
                    .expect("phase 2 aborted");

    tv.add("expand");

    let krate = phase_2_configure_and_expand_without_std_inject(&sess, krate, 
                                                                "a", None)
        .expect("phase 2 aborted");

    tv.add("expand2");

    let mut forest = ast_map::Forest::new(krate);
    let arenas = ty::CtxtArenas::new();
    let ast_map = driver::assign_node_ids_and_map(&sess, &mut forest);
    tv.add("ast map");

    let krate = ast_map.krate();
    CrateReader::new(&sess).read_crates(krate);

    tv.add("read crates");

    let lang_items = lang_items::collect_language_items(krate, &sess);
    let resolve::CrateMap {
        def_map,
        freevars,
        export_map,
        trait_map,
        ..
    } = resolve::resolve_crate(&sess, &ast_map, 
                               &lang_items, krate, resolve::MakeGlobMap::No);

    tv.add("resolve crate");

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

    tv.add("mk_ctxt");

    // The following is from typeck::check_crate(&ty_cx, trait_map);
    let ccx = CrateCtxt {
        trait_map: trait_map,
        all_traits: RefCell::new(None),
        tcx: &tcx
    };

    collect::collect_item_types(&tcx);

    tv.add("collect_item_types");

    variance::infer_variance(&tcx);

    tv.add("infer variance");


    // Can we do without coherence checking?

    // this is from     coherence::check_coherence(&ccx);
    coherence::CoherenceChecker {
        crate_context: &ccx,
        inference_context: new_infer_ctxt(ccx.tcx),
        inherent_impls: RefCell::new(FnvHashMap()),
    }.check(&ccx.tcx.map.krate());

    tv.add("coherence check");


    //check::check_item_types(&ccx);
    check_item_types2(&ccx);

    tv.add("type check");

    for (s, time, duration) in tv.tv {
        println!("t {}: {} \t {}",duration, time - tv.t0, s);
    }
 
    // println!("PHIL node_types is {:?}\n",tcx.node_types());
    // println!("PHIL def_map is {:?}\n",tcx.def_map);
    // println!("PHIL krate is {:?}",krate);

    print_expr_types(&tcx, &krate);
    println!("DONE");
}


use mytypeck::check::{wf,dropck};
use mytypeck::check::{CheckItemTypesVisitor, CheckItemBodiesVisitor};

pub fn check_item_types(ccx: &CrateCtxt) {

    let mut tv = Timer::new();

    let krate = ccx.tcx.map.krate();
    let mut visit = wf::CheckTypeWellFormedVisitor::new(ccx);
    visit::walk_crate(&mut visit, krate);

    // If types are not well-formed, it leads to all manner of errors
    // downstream, so stop reporting errors at this point.
    ccx.tcx.sess.abort_if_errors();
    tv.add("check well formed");

    let mut visit = CheckItemTypesVisitor { ccx: ccx };
    visit::walk_crate(&mut visit, krate);

    ccx.tcx.sess.abort_if_errors();
    tv.add("check item types");

    let mut visit = CheckItemBodiesVisitor { ccx: ccx };
    visit::walk_crate(&mut visit, krate);
    tv.add("check item bodies");
    ccx.tcx.sess.abort_if_errors();

    for drop_method_did in ccx.tcx.destructors.borrow().iter() {
        if drop_method_did.krate == ast::LOCAL_CRATE {
            let drop_impl_did = ccx.tcx.map.get_parent_did(drop_method_did.node);
            match dropck::check_drop_impl(ccx.tcx, drop_impl_did) {
                Ok(()) => {}
                Err(()) => {
                    assert!(ccx.tcx.sess.has_errors());
                }
            }
        }
    }
    tv.add("drop method checking");

    ccx.tcx.sess.abort_if_errors();
    for (s, time, duration) in tv.tv {
        println!("t {}: {} \t {}",duration, time - tv.t0, s);
    }
}


pub fn check_item_types2(ccx: &CrateCtxt) {
    let mut tv = Timer::new();

    let krate = ccx.tcx.map.krate();
    // let mut visit_ = wf::CheckTypeWellFormedVisitor::new(ccx);
    // visit::walk_crate(&mut visit_, krate);

    // // If types are not well-formed, it leads to all manner of errors
    // // downstream, so stop reporting errors at this point.
    // ccx.tcx.sess.abort_if_errors();
    // tv.add("check well formed");

    let mut visit_ = CheckItemTypesVisitor { ccx: ccx };
    visit::walk_crate(&mut visit_, krate);

    ccx.tcx.sess.abort_if_errors();
    tv.add("check item types");

    //let mut visit_ = CheckItemBodiesVisitor { ccx: ccx };
    //visit::walk_crate(&mut visit_, krate);
    //visit::walk_block(&mut visit_, v.0.unwrap());

    //tv.add("check item bodies");
    //ccx.tcx.sess.abort_if_errors();

    //visit::walk_crate(&mut visit_, krate);
    //visit::walk_block(&mut visit_, v.0.unwrap());

    //tv.add("check item bodies");
    //ccx.tcx.sess.abort_if_errors();

    //struct FnFinder<'a>(Option<&'a ast::Block>);
    struct FnFinder<'a, 'tcx: 'a> {
        typechecker: CheckItemBodiesVisitor<'a, 'tcx>
    };

    impl<'a, 'tcx: 'a> visit::Visitor<'tcx> for FnFinder<'a, 'tcx> {

        fn visit_item(&mut self, i: &'tcx ast::Item) {
            //println!("PHIL visit_item {:?} '{}'",i.ident, i.ident.as_str());

            if i.ident.as_str() == "check" {
                visit::walk_item(self, i);
            }
            if i.ident.as_str() == "check_bounds_are_used" {
                println!("PHIL FOUND!!");
                // run the type checker on it
                self.typechecker.visit_item(i);
            }

        }
    }
    
    let mut visit_ = CheckItemBodiesVisitor { ccx: ccx };
    let mut v = FnFinder{ typechecker: visit_ };
    visit::walk_crate(&mut v, krate);
    tv.add("check target item body");



    for drop_method_did in ccx.tcx.destructors.borrow().iter() {
        if drop_method_did.krate == ast::LOCAL_CRATE {
            let drop_impl_did = ccx.tcx.map.get_parent_did(drop_method_did.node);
            match dropck::check_drop_impl(ccx.tcx, drop_impl_did) {
                Ok(()) => {}
                Err(()) => {
                    assert!(ccx.tcx.sess.has_errors());
                }
            }
        }
    }
    tv.add("drop method checking");

    ccx.tcx.sess.abort_if_errors();
    for (s, time, duration) in tv.tv {
        println!("t {}: {} \t {}",duration, time - tv.t0, s);
    }
}




use rustc::util::common::time;
use rustc_driver::driver::collect_crate_types;
use rustc_driver::driver::collect_crate_metadata;
use rustc::middle;
use rustc::metadata;
use rustc::plugin;
use rustc::plugin::registry::Registry;
use syntax::diagnostics;
use std::ffi::OsString;
use std::env;
use rustc::session::search_paths::PathKind;

pub fn phase_2_configure_and_expand_without_std_inject(sess: &session::Session,
                                                       mut krate: ast::Crate,
                                                       crate_name: &str,
                                                   addl_plugins: Option<Vec<String>>)
                                                       -> Option<ast::Crate> {
    let mut tv = Timer::new();

    let time_passes = sess.time_passes();

    // strip before anything else because crate metadata may use #[cfg_attr]
    // and so macros can depend on configuration variables, such as
    //
    //   #[macro_use] #[cfg(foo)]
    //   mod bar { macro_rules! baz!(() => {{}}) }
    //
    // baz! should not use this definition unless foo is enabled.

    // krate = time(time_passes, "configuration 1", krate, |krate|
    //              syntax::config::strip_unconfigured_items(sess.diagnostic(), krate));

    // *sess.crate_types.borrow_mut() =
    //     collect_crate_types(sess, &krate.attrs);
    // *sess.crate_metadata.borrow_mut() =
    //     collect_crate_metadata(sess, &krate.attrs);

    // time(time_passes, "recursion limit", (), |_| {
    //     middle::recursion_limit::update_recursion_limit(sess, &krate);
    // });

    // time(time_passes, "gated macro checking", (), |_| {
    //     let features =
    //         syntax::feature_gate::check_crate_macros(sess.codemap(),
    //                                                  &sess.parse_sess.span_diagnostic,
    //                                                  &krate);

    //     // these need to be set "early" so that expansion sees `quote` if enabled.
    //     *sess.features.borrow_mut() = features;
    //     sess.abort_if_errors();
    // });
 

    // krate = time(time_passes, "crate injection", krate, |krate|
    //              syntax::std_inject::maybe_inject_crates_ref(krate,
    //                                                          sess.opts.alt_std_name.clone()));

    let macros = time(time_passes, "macro loading", (), |_|
        metadata::macro_import::read_macro_defs(sess, &krate));

    tv.add("macro loading");
    let mut addl_plugins = Some(addl_plugins);
    let registrars = time(time_passes, "plugin loading", (), |_|
        plugin::load::load_plugins(sess, &krate, addl_plugins.take().unwrap()));

    tv.add("plugin loading");
    let mut registry = Registry::new(sess, &krate);

    time(time_passes, "plugin registration", registrars, |registrars| {
        if sess.features.borrow().rustc_diagnostic_macros {
            registry.register_macro("__diagnostic_used",
                diagnostics::plugin::expand_diagnostic_used);
            registry.register_macro("__register_diagnostic",
                diagnostics::plugin::expand_register_diagnostic);
            registry.register_macro("__build_diagnostic_array",
                diagnostics::plugin::expand_build_diagnostic_array);
        }

        for registrar in registrars {
            registry.args_hidden = Some(registrar.args);
            (registrar.fun)(&mut registry);
        }
    });

    tv.add("plugin registration");

    let Registry { syntax_exts, lint_passes, lint_groups,
                   llvm_passes, attributes, .. } = registry;

    {
        let mut ls = sess.lint_store.borrow_mut();
        for pass in lint_passes {
            ls.register_pass(Some(sess), true, pass);
        }

        for (name, to) in lint_groups {
            ls.register_group(Some(sess), true, name, to);
        }

        *sess.plugin_llvm_passes.borrow_mut() = llvm_passes;
        *sess.plugin_attributes.borrow_mut() = attributes.clone();
    }


    tv.add("plugin registration2");

    // // Lint plugins are registered; now we can process command line flags.
    // if sess.opts.describe_lints {
    //     //super::describe_lints(&*sess.lint_store.borrow(), true);
    //     return None;
    // }
    // sess.lint_store.borrow_mut().process_command_line(sess);

    // Abort if there are errors from lint processing or a plugin registrar.
    sess.abort_if_errors();

    krate = time(time_passes, "expansion", (krate, macros, syntax_exts),
        |(krate, macros, syntax_exts)| {
            // Windows dlls do not have rpaths, so they don't know how to find their
            // dependencies. It's up to us to tell the system where to find all the
            // dependent dlls. Note that this uses cfg!(windows) as opposed to
            // targ_cfg because syntax extensions are always loaded for the host
            // compiler, not for the target.
            let mut _old_path = OsString::new();
            if cfg!(windows) {
                _old_path = env::var_os("PATH").unwrap_or(_old_path);
                let mut new_path = sess.host_filesearch(PathKind::All)
                                       .get_dylib_search_paths();
                new_path.extend(env::split_paths(&_old_path));
                env::set_var("PATH", &env::join_paths(new_path.iter()).unwrap());
            }
            let features = sess.features.borrow();
            let cfg = syntax::ext::expand::ExpansionConfig {
                crate_name: crate_name.to_string(),
                features: Some(&features),
                recursion_limit: sess.recursion_limit.get(),
                trace_mac: sess.opts.debugging_opts.trace_macros,
            };
            let ret = syntax::ext::expand::expand_crate(&sess.parse_sess,
                                              cfg,
                                              macros,
                                              syntax_exts,
                                              krate);
            if cfg!(windows) {
                env::set_var("PATH", &_old_path);
            }
            ret
        }
    );

    tv.add("expansion");

    // Needs to go *after* expansion to be able to check the results
    // of macro expansion.  This runs before #[cfg] to try to catch as
    // much as possible (e.g. help the programmer avoid platform
    // specific differences)
    time(time_passes, "complete gated feature checking 1", (), |_| {
        let features =
            syntax::feature_gate::check_crate(sess.codemap(),
                                              &sess.parse_sess.span_diagnostic,
                                              &krate, &attributes);
        *sess.features.borrow_mut() = features;
        sess.abort_if_errors();
    });

    tv.add("gated feature checking");
    // JBC: make CFG processing part of expansion to avoid this problem:

    // strip again, in case expansion added anything with a #[cfg].
    krate = time(time_passes, "configuration 2", krate, |krate|
                 syntax::config::strip_unconfigured_items(sess.diagnostic(), krate));

    tv.add("strip cfg");

    krate = time(time_passes, "maybe building test harness", krate, |krate|
                 syntax::test::modify_for_testing(&sess.parse_sess,
                                                  &sess.opts.cfg,
                                                  krate,
                                                  sess.diagnostic()));
    tv.add("maybe build test harness");
    // krate = time(time_passes, "prelude injection", krate, |krate|
    //              syntax::std_inject::maybe_inject_prelude(krate));

    time(time_passes, "checking that all macro invocations are gone", &krate, |krate|
         syntax::ext::expand::check_for_macros(&sess.parse_sess, krate));

    tv.add("check macro invocations are gone");
    // One final feature gating of the true AST that gets compiled
    // later, to make sure we've got everything (e.g. configuration
    // can insert new attributes via `cfg_attr`)
    time(time_passes, "complete gated feature checking 2", (), |_| {
        let features =
            syntax::feature_gate::check_crate(sess.codemap(),
                                              &sess.parse_sess.span_diagnostic,
                                              &krate, &attributes);
        *sess.features.borrow_mut() = features;
        sess.abort_if_errors();
    });

    tv.add("complete feature gate checking");

    for (s, time, duration) in tv.tv {
        println!("phase2 {}: {} \t {}",duration, time - tv.t0, s);
    }
    Some(krate)
}


fn main() {
    //try_modify_crate();
    try_resolve_expr_types();
}



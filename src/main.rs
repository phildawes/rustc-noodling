#![feature(rustc_private)]

extern crate rustc;
extern crate syntax;
extern crate rustc_driver;
extern crate rustc_lint;
extern crate rustc_front;
extern crate rustc_resolve;

extern crate time;

// PD: patched rustc_typeck to allow access to some elements. see mytypeck.patch
extern crate mytypeck;

mod findlibs;
mod codecleaner;
mod stripper;
mod codeiter;

use stripper::StrippedFileLoader;

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
use mytypeck::middle::ty;
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
use rustc_front::visit;
use rustc_front::hir;

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
        // panic!("PHIL PANICING2 {:?} msg={}",lvl, msg);
    }

    fn custom_emit(&mut self,
                   _cm: &codemap::CodeMap,
                   _sp: RenderSpan,
                   msg: &str,
                   lvl: Level)
    {
        println!("PHIL {:?} msg={}",lvl, msg);
        //panic!("PHIL PANICING {:?} msg={}",lvl, msg);
    }
}


pub fn get_region_coords(args: &[String]) -> ((i32,i32), (i32,i32)){
    let linenum = args[0].parse().unwrap();
    let col = args[1].parse().unwrap();
    let other_line = args[2].parse().unwrap();
    let other_col = args[3].parse().unwrap();

    let (lo, hi);
    if linenum == other_line {
        if col > other_col {
            lo = (linenum, other_col); hi = (linenum, col);
        } else {
            lo = (linenum, col); hi = (linenum, other_col);
        }
    } else if linenum > other_line {
        lo = (other_line, other_col); hi = (linenum, col);
    } else {
        lo = (linenum, col); hi = (other_line, other_col);
    }
    (lo, hi)
}

pub fn run_type_inference() {
    let emitter = Box::new(MyErrorEmitter);

    env::set_var("CFG_COMPILER_HOST_TRIPLE","x86_64-unknown-linux-gnu");
    let args: Vec<String> = std::env::args().collect();
    let (lo,hi) = get_region_coords(&args[1..5]);
    let tmpfname = &args[5];

    let fname = if args.len() > 6 { &args[6] } else { tmpfname };

    println!("fname: {}, lo {:?}, hi {:?}", fname, lo, hi);
    let mut options = config::basic_options();

    let fpath = Path::new(&fname);

    let mut rootfpath = fpath.to_path_buf();

    if let Some(cargopath) = findlibs::find_cargo_tomlfile(fpath) {
        println!("found cargo root: {:?}",cargopath);
        rootfpath = findlibs::main_file(&cargopath);
        //options.search_paths.add_path();
        let deppath = findlibs::dependency_path(&cargopath);
        //options.search_paths.paths.push((PathKind::Dependency, deppath));
        let depath = format!("dependency={}", deppath.as_os_str().to_str().unwrap());
        options.search_paths.add_path(&depath, diagnostic::ColorConfig::Auto);

        for (libname, libpath) in findlibs::list_libs(&cargopath) {
            let mut v = Vec::new();
            v.push(libpath.into_os_string().into_string().unwrap());
            options.externs.insert(libname, v);
        }
    } else {
        if let Some(path) = findlibs::find_librs(fpath) {
            println!("found root lib file: {:?}",path);
            rootfpath = path;
        }
    }

    // setup options
    options.debugging_opts.verbose = true;
    options.unstable_features = UnstableFeatures::Allow;

    let mut crate_types = Vec::new();
    crate_types.push(config::CrateType::CrateTypeExecutable);
    options.crate_types = crate_types;

    options.maybe_sysroot = Some(Path::new("/home/pld/.multirust/toolchains/nightly/").to_path_buf());

    // stripped file loader strips the bodies of fns that we aren't interested in
    let codemap = CodeMap::with_file_loader(Box::new(StrippedFileLoader{ 
        fname: fname.clone(),
        tmpfname: tmpfname.clone(),
        coords: (lo.0 as usize, lo.1 as usize),
    }));
    let diagnostic_handler =
        diagnostic::Handler::with_emitter(true, emitter);
    let span_diagnostic_handler =
        diagnostic::SpanHandler::new(diagnostic_handler, codemap);

    let t0 = time::precise_time_s();
    ///////// create session
    let sess = session::build_session_(options, None, span_diagnostic_handler);

    // rustc_lint::register_builtins(&mut sess.lint_store.borrow_mut(), Some(&sess));
    let krate_config = Vec::new();

    let input = config::Input::File(rootfpath);

    ////////  Phase 1 + 2
    let krate = driver::phase_1_parse_input(&sess, krate_config, &input);
    let krate = driver::phase_2_configure_and_expand(&sess, krate, "test", None)
                    .expect("phase 2 aborted");
    let t1 = time::precise_time_s();
    println!("PHIL 0: expand complete {:.3}s",t1-t0);

    let t0 = time::precise_time_s();
    ///////// Assign ids
    let krate = driver::assign_node_ids(&sess, krate);
    let mut hir_forest = hir_map::Forest::new(lower_crate(&krate));
    let arenas = ty::CtxtArenas::new();
    let ast_map = driver::make_map(&sess, &mut hir_forest);


    ///////// PD: phase 3 analysis passes
    let krate = ast_map.krate();


    metadata::creader::LocalCrateReader::new(&sess, &ast_map).read_crates(krate);

    let lang_items = lang_items::collect_language_items(krate, &sess);
    let m = resolve::resolve_crate(&sess, &ast_map, resolve::MakeGlobMap::No);

    let resolve::CrateMap { def_map, freevars, trait_map, .. } = m;

    syntax::ext::mtwt::clear_tables();

    let named_region_map = resolve_lifetime::krate(&sess, krate, &def_map);


    //mytypeck::middle::entry::find_entry_point(&sess, &ast_map);

    // PD: maybe don't need this
    sess.plugin_registrar_fn.set(
        plugin::build::find_plugin_registrar(sess.diagnostic(), krate));
    
    let region_map = region::resolve_crate(&sess, krate);

    // PD: maybe don't need this
    rustc::middle::check_loop::check_crate(&sess, krate);
    rustc::middle::check_static_recursion::check_crate(&sess, krate, &def_map, &ast_map);
    let t1 = time::precise_time_s();
    println!("PHIL 0: pre-typeck complete {:.3}s",t1-t0);

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
           // passes are timed inside typeck

           let t0 = time::precise_time_s();
           let ccx = CrateCtxt {
               trait_map: trait_map,
               all_traits: RefCell::new(None),
               tcx: tcx
           };

           // mytypeck::check_crate(tcx, trait_map);
           collect::collect_item_types(tcx);

           //tcx.sess.abort_if_errors();

           println!("PHIL 1");

           mytypeck::variance::infer_variance(tcx);

           println!("PHIL 2");
           coherence::check_coherence(&ccx);

           println!("PHIL 3");
           check::check_wf_old(&ccx);

           println!("PHIL 4");
           check::check_item_types(&ccx);

           println!("PHIL 5");
           //check::check_item_bodies(&ccx);

           let t1 = time::precise_time_s();
           println!("typeck items: {:.3}s",t1 - t0);

           let t0 = time::precise_time_s();
           let krate = ccx.tcx.map.krate();
           let mut visit = MyCheckItemBodiesVisitor { 
               ccx: &ccx, 
               tables: RefCell::new(ty::Tables::empty()),
               fname: fname.clone(),
               lo: lo,
               hi: hi,
           };
           visit::walk_crate(&mut visit, krate);

           let t1 = time::precise_time_s();
           println!("check bodies: {:.3}s",t1 - t0);

           // println!("PHIL tcx node_types {:?} ", tcx.tables.borrow().node_types);
           // println!("PHIL tcx item_substs {:?} ", tcx.tables.borrow().item_substs);

           println!("PHIL 6");
           // check::check_drop_impls(&ccx);
           // println!("PHIL 7");
           // check::check_wf_new(&ccx);

           // tcx.sess.abort_if_errors();
           println!("running print_expr_types");
           let t0 = time::precise_time_s();
           print_expr_types(&tcx, krate, fname, lo, hi, visit.tables);
           let t1 = time::precise_time_s();
           println!("print types: {:.3}s",t1 - t0);
       });
}

fn print_expr_types<'a, 'tcx>(tcx: &'a ty::ctxt<'tcx>, 
                              krate: &'a hir::Crate,
                              fname: &str,
                              lo: (i32,i32),
                              hi: (i32,i32),
                              tables: RefCell<ty::Tables<'tcx>>,
                              ) {

    struct MyExprVisitor<'a, 'tcx: 'a> {
        tcx: &'a ty::ctxt<'tcx>, 
        fname: String,
        lo: (i32, i32),
        hi: (i32, i32),
        ty_: String,
        tables: RefCell<ty::Tables<'tcx>>,
    };

    impl<'a, 'tcx> visit::Visitor<'a> for MyExprVisitor<'a, 'tcx> {
        fn visit_item(&mut self, i: &'a hir::Item) {
            visit::walk_item(self, i);
        }
        fn visit_expr(&mut self, ex: &'a hir::Expr) {
            let tcx = self.tcx;
            //let ty_ = tcx.expr_ty_adjusted(ex);
            
            let codemap: &CodeMap = tcx.sess.codemap();
            let fname = codemap.span_to_filename(ex.span);
            let loloc = codemap.lookup_char_pos(ex.span.lo);
            let hiloc = codemap.lookup_char_pos(ex.span.hi);
            let locol = loloc.col.0 as i32;
            let hicol = hiloc.col.0 as i32;

            if self.fname == fname
                && self.lo.0 == loloc.line as i32
                && self.hi.0 == hiloc.line as i32
                && self.lo.1 == locol
                && self.hi.1 == hicol {

                    let mut ty_ = tcx.expr_ty_opt(ex);
                    if None == ty_ {
                        println!("PHIL ty_ was None!! Trying function table");
                        ty_ = self.tables.borrow().node_types.get(&ex.id).map(|a| *a)
                    } 
                    if None == ty_ {
                        println!("PHIL ty_ was None!!");
                        return;
                    }
                    let ty_ = ty_.unwrap();

                println!("PHIL ty is {}",ty_);
                println!("PHIL span is {:?}", ex.span);
                println!("PHIL fname is {}, line is {}, col is {}",fname,
                             loloc.line,
                             loloc.col.0);
                self.ty_ = format!("{}",ty_);
            }

            visit::walk_expr(self, ex);
        }
    }

    let mut v = MyExprVisitor {
        tcx: tcx,
        fname: fname.to_string(),
        lo: lo,
        hi: hi,
        ty_: String::new(),
        tables: tables,
    };

    visit::walk_crate(&mut v, krate);

    if v.ty_ == "" {
        println!("NO TYPE MATCH");
    } else {
        println!("TYPE {}", v.ty_);
    }
}


pub struct MyCheckItemBodiesVisitor<'a, 'tcx: 'a> { 
    pub ccx: &'a CrateCtxt<'a, 'tcx>,
    pub tables: RefCell<ty::Tables<'tcx>>,
    pub fname: String,
    pub lo: (i32,i32),
    pub hi: (i32,i32),
}

impl<'a, 'tcx> visit::Visitor<'tcx> for MyCheckItemBodiesVisitor<'a, 'tcx> {
    fn visit_item(&mut self, i: &'tcx hir::Item) {
        let tcx = self.ccx.tcx;
        let codemap: &CodeMap = tcx.sess.codemap();
        let fname = codemap.span_to_filename(i.span);
        let loloc = codemap.lookup_char_pos(i.span.lo);
        let hiloc = codemap.lookup_char_pos(i.span.hi);
        let locol = loloc.col.0 as i32;
        let hicol = hiloc.col.0 as i32;

        //println!("{}, {}",self.fname, fname);
        if self.fname == fname && is_in(self.lo, 
                                        self.hi, 
                                        (loloc.line as i32,locol), 
                                        (hiloc.line as i32,hicol)) {
            println!("PHIL found the body!");
            self.tables = check::check_item_body(self.ccx, i);
            //println!("PHIL tables is {:?}", self.tables.borrow().node_types);
        }
        visit::walk_item(self, i);

    }
}

fn is_in(lo: (i32,i32), 
         hi: (i32,i32),
         lo_a: (i32,i32),
         hi_a: (i32,i32)) -> bool {
    if lo.0 < lo_a.0 || (lo.0 == lo_a.0 && lo.1 < lo_a.1) {
        return false;
    }

    if hi.0 > hi_a.0 || (hi.0 == hi_a.0 && hi.1 > hi_a.1) {
        return false;
    }
    true
}


fn main() {
    run_type_inference();
}

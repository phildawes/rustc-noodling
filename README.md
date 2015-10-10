** rustc noodling

An attempt to get type information out of rustc as fast as possible

Created by looking at rustc_driver/test.rs test_env() and recreating


Running: 

cd ~/src/rust/rustc-noodling/; source ./env && RUST_BACKTRACE=1 cargo run --release ~/tmp/a1.rs 5 4 5 5


cd ~/src/rust/rustc-noodling/; source ./env && RUST_BACKTRACE=1 cargo run --release 696 28 696 55 /usr/local/src/rust/src/librustc_typeck/variance.rs 


Notes:

librustc README.md contains info about the whole crate loading process

rustc::metadata is the module containing all the stuff

An rlib is an 'ar' archive, containing a metadata binary file.
   Metadata is incoded in RBML (really bad markup language). See librbml
librustc::metadata::decoder contains code to decode the metadata file


- It seems that if a function doesn't return anything then that part doesn't get checked on the body check.





Changes to mytypeck:

 - made some structs public
 - bare_fn returns the tables node that it used for typechecking, even if it fails
   - that allows lookup fn to resolve a type even if it didn't typeck properly
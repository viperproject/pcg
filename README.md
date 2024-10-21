# Setup

Our implementation requires a custom version of Rust that instructs Polonius to
dump additional data. The version is available here:
https://github.com/zgrannan/rust/tree/pcs

To setup the toolchain correctly, do the following in other directory (e.g. $HOME):

1. `git clone -b pcs https://github.com/zgrannan/rust.git`
2. `cd rust`
3. `./x.py build --stage 2`
4. Confirm that the folder `build/PLATFORM/stage2` exists (
   where `PLATFORM` is e.g. `aarch64-apple-darwin`)
5. `rustup toolchain link NAME build/PLATFORM/stage2`, where `PLATFORM` is the
   platform above and NAME is some name you've decided
6. Modify the `rust-toolchain` file in this directory with the new name by
   setting `channel = "NAME"`
   
At this point you can compile this crate by running `cargo build` from this
directory. If cargo complains that the toolchain doesn't have THING installed,
then run `./x.py build --stage 2 THING` from the `rust` directory and try again.

# Running
To run:

`cargo run [FILENAME].rs`

To view the visualization 

1. `PCS_VISUALIZATION=true cargo run [FILENAME.rs]`
2. `cd visualization && ./serve`
3. Go to http://localhost:8080 and select the function you wish to view

Once the server is running, you can keep it running and analyze other files
(e.g. `cargo run [FILENAME2].rs`). Just refresh the page to see updated results.

To run on the top crates use:

`cargo test --package pcs --test top_crates -- top_crates --exact --show-output`

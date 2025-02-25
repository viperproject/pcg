# Running
To run:

`cargo run [FILENAME].rs`

To view the visualization

1. `PCG_VISUALIZATION=true cargo run [FILENAME.rs]`
2. `cd visualization && ./serve`
3. Go to http://localhost:8080 and select the function you wish to view

Once the server is running, you can keep it running and analyze other files
(e.g. `cargo run [FILENAME2].rs`). Just refresh the page to see updated results.

To run on the top crates use:

`cargo test --test top_crates -- --ignored`

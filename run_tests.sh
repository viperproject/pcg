#!/bin/bash

# Run cargo build first to ensure the executable is up to date
cargo build

# Loop through all .rs files in tests directory
for test_file in tests/[0-9]*.rs; do
    echo "Running test: $test_file"
    cargo run -- "$test_file"

    # Check exit status
    if [ $? -ne 0 ]; then
        echo "Failed on $test_file"
        exit 1
    fi
done

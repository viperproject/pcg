#!/usr/bin/env bash
#
# This scripts identifies validity assertion failures from the PCG log output
# and extracts the stringified version of the test cases that reproduce the
# failures (see `selected_crates.rs`).
#
# Example usage:
#
# The following command will run PCG on the functions in the top 500 crates and report
# validity errors instead of crashing on them. The log output will be sent to the file `out`.
# env PCG_VALIDITY_CHECKS=true PCG_VALIDITY_CHECKS_WARN_ONLY=true PCG_TEST_CRATE_PARALLELISM=12 cargo test --test top_crates -- --nocapture --ignored >out 2>&1
#
# Then, the following command will extract the stringified test cases from
# failures written to the log output:
# ./extract_failures.sh out

input="$1"

awk -F'To reproduce this failure, use test case:' '
    NF > 1 {
        # Trim leading/trailing spaces
        str = $2
        gsub(/^[ \t]+|[ \t]+$/, "", str)
        # Count semicolons
        n = gsub(/;/, ";", str)
        if (n == 4) print str
    }
' "$input" |
sort -t ';' -k5,5n -u

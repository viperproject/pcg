#!/usr/bin/env bash
# Usage: ./filter_sort_repro.sh input.txt

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
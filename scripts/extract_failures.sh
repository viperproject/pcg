#!/usr/bin/env bash
# Usage: ./filter_sort_lastword.sh input.txt

input="$1"

awk '{
    last = $NF
    n = gsub(/;/, ";", last)
    if (n == 4) print last
}' "$input" |
sort -t ';' -k5,5n -u
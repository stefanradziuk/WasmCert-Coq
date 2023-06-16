#!/usr/bin/env bash

# for n in 0 10 20; do
for n in 0 10 20 30 40 50 60 100 1000 2000 5000 10000 15000 20000; do
  log="bench-out-old-$n"
  touch "$log"

  for i in {1..5}; do
    echo "n = $n, i = $i"
    sed 's/(\*n\*)/'"$n"'/' repl-itp.ml \
      | ocaml \
      | rg -e '\d\.\d{6}s' -e '\si64\.const' \
      >> "$log"
  done

done


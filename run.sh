#!/bin/bash

dune build
dune exec ./main.exe "$@"

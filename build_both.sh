#!/bin/bash

pushd value_set
make
make reinstall
popd
pushd explicit_edge
make clean
make
make reinstall
popd

#!/bin/sh

rand_build () 
{ 
    local seed=${1}
    local target=${2}
    clang -frandom-seed=$1 -mllvm -shuffle-stack-frames -mllvm -max-stack-pad-size=64 -mllvm -randomize-machine-registers ${target}.c -o ${target}-${seed}
}


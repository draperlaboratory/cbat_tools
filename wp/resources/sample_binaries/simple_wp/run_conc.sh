#!/bin/bash

set -x;

bap main \
    --pass=run \
    --run-entry-points=main \
    --conc-pre \
    --conc-subroutine=main \
    --conc-stops \
    --conc-regio

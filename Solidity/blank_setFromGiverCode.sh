#!/bin/bash
everdev contract run Blank -a $1 setFromGiverCodeHash --input "code_hash:0x`./gethash.sh FromGiver.tvc`,code_depth:`./getdepth.sh FromGiver.tvc`" --signer keys1

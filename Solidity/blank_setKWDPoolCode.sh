#!/bin/bash
everdev contract run Blank -a $1 setKWDPoolCodeHash --input "code_hash:0x`./gethash.sh KWDPool.tvc`,code_depth:`./getdepth.sh KWDPool.tvc`" --signer keys1

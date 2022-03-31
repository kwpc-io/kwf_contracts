#!/bin/bash
everdev contract run Blank -a $1 deployFromGiver --input "code:\"`./getimage.sh FromGiver.tvc`\",giver:\"$2\",nonce:$3" --signer keys1

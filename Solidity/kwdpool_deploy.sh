#!/bin/bash
# uint256 static nonce_
everdev contract deploy KWDPool --data "fund_address_:\"$1\",nonce_:$2" --input "final_address:\"$3\"" --signer keys1 -v $4

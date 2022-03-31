#!/bin/bash

# script requires some python packages before running:
# python3 -m venv .venv
# source .venv/bin/activate
# pip install ton-client-py
# pip install aiohttp

VOTING_TIME=$((4*60))
#finalize all contracts

#finalize all contracts
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$FROM_GIVER1_ADDRESS\",force_giveup:false"  --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL1_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL2_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL3_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL4_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL5_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL6_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL7_ADDRESS\",force_giveup:false" --signer keys1


#start voting
everdev contract run Blank -a $BLANK_ADDRESS startVoting --input "voting_time:$VOTING_TIME,code_hash:0x`./gethash.sh PseudoFund.tvc`" --signer keys1

#Vote1
everdev contract run KWDPool -a $KWD_POOL1_ADDRESS vote --input "choice:true,voting_id:0,code_hash:0x`./gethash.sh PseudoFund.tvc`" --signer keys1

#Vote2
everdev contract run KWDPool -a $KWD_POOL2_ADDRESS vote --input "choice:true,voting_id:0,code_hash:0x`./gethash.sh PseudoFund.tvc`" --signer keys1
#Vote3
everdev contract run KWDPool -a $KWD_POOL3_ADDRESS vote --input "choice:false,voting_id:0,code_hash:0x`./gethash.sh PseudoFund.tvc`" --signer keys1

#Vote7
everdev contract run KWDPool -a $KWD_POOL7_ADDRESS vote --input "choice:true,voting_id:0,code_hash:0x`./gethash.sh PseudoFund.tvc`" --signer keys1


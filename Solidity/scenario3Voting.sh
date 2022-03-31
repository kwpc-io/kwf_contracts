#!/bin/bash

# script requires some python packages before running:
# python3 -m venv .venv
# source .venv/bin/activate
# pip install ton-client-py
# pip install aiohttp


#setCode
everdev contract run Blank -a $BLANK_ADDRESS setFundCode --input "code:\"`./getimage.sh PseudoFund.tvc`\"" --signer keys1


#get Funds
everdev contract run PseudoFund -a $BLANK_ADDRESS getFromGiverFunds --input "from_giver_address:\"$FROM_GIVER1_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL1_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL2_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL3_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL4_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL5_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL6_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL7_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1

everdev contract run PseudoFund -a $BLANK_ADDRESS killFund --input "address_to:\"$MY_ADDRESS\"" --signer keys1



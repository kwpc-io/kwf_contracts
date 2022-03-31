#!/bin/bash

# finalize all contracts for Blank2 
everdev contract run Blank -a $BLANK_ADDRESS2 finalize --input "addr:\"$KWD_POOL1_2_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS2 finalize --input "addr:\"$KWD_POOL2_2_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS2 finalize --input "addr:\"$KWD_POOL3_2_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS2 finalize --input "addr:\"$FROM_GIVER1_2_ADDRESS\""  --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS2 finalize --input "addr:\"$FROM_GIVER2_2_ADDRESS\""  --signer keys1


#try get Funds Blank2 by Blank1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL1_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL2_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL3_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$FROM_GIVER1_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$FROM_GIVER2_2_ADDRESS\"" --signer keys1



#setCode
everdev contract run Blank -a $BLANK_ADDRESS2 setFundCode --input "code:\"`./getimage.sh PseudoFund.tvc`\"" --signer keys1




# get Funds Blank2 
everdev contract run PseudoFund -a $BLANK_ADDRESS2 getFunds --input "kwdp_address:\"$KWD_POOL1_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS2 getFunds --input "kwdp_address:\"$KWD_POOL2_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS2 getFunds --input "kwdp_address:\"$KWD_POOL3_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS2 getFunds --input "kwdp_address:\"$FROM_GIVER1_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS2 getFunds --input "kwdp_address:\"$FROM_GIVER2_2_ADDRESS\"" --signer keys1


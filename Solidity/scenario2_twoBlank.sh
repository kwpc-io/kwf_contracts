#!/bin/bash

#finalize all contracts for Blank1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$KWD_POOL1_1_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$KWD_POOL2_1_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$KWD_POOL3_1_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$FROM_GIVER1_1_ADDRESS\""  --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$FROM_GIVER2_1_ADDRESS\""  --signer keys1
#try finalize all contracts for Blank2 by blank1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$KWD_POOL1_2_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$KWD_POOL2_2_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$KWD_POOL3_2_ADDRESS\"" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$FROM_GIVER1_2_ADDRESS\""  --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS1 finalize --input "addr:\"$FROM_GIVER2_2_ADDRESS\""  --signer keys1

#topup
RESPAWN_SUMMA=50000000000
everdev contract topup Blank -a $BLANK_ADDRESS1 --signer keys1 --value $RESPAWN_SUMMA --signer keys1

#setCode
everdev contract run Blank -a $BLANK_ADDRESS1 setFundCode --input "code:\"`./getimage.sh PseudoFund.tvc`\"" --signer keys1


#get Funds
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL1_1_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL2_1_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL3_1_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$FROM_GIVER1_1_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$FROM_GIVER2_1_ADDRESS\"" --signer keys1


#try get Funds Blank2 by Blank1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL1_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL2_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$KWD_POOL3_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$FROM_GIVER1_2_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS1 getFunds --input "kwdp_address:\"$FROM_GIVER2_2_ADDRESS\"" --signer keys1

#topup
RESPAWN_SUMMA=50000000000
everdev contract topup Blank -a $BLANK_ADDRESS2 --signer keys1 --value $RESPAWN_SUMMA --signer keys1

#try setCode Blank2
everdev contract run Blank -a $BLANK_ADDRESS2 setFundCode --input "code:\"`./getimage.sh PseudoFund.tvc`\"" --signer keys1

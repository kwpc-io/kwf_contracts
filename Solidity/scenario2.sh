#!/bin/bash

#finalize all contracts
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL1_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$KWD_POOL2_ADDRESS\",force_giveup:false" --signer keys1
everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$FROM_GIVER1_ADDRESS\",force_giveup:false"  --signer keys1

#topup
RESPAWN_SUMMA=50000000000
everdev contract topup Blank -a $BLANK_ADDRESS --signer keys1 --value $RESPAWN_SUMMA --signer keys1

#setCode
everdev contract run Blank -a $BLANK_ADDRESS setFundCode --input "code:\"`./getimage.sh PseudoFund.tvc`\"" --signer keys1


#get Funds
everdev contract run PseudoFund -a $BLANK_ADDRESS getFromGiverFunds --input "from_giver_address:\"$FROM_GIVER1_ADDRESS\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL1_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1
everdev contract run PseudoFund -a $BLANK_ADDRESS transferFundsTo --input "kwdp_address:\"$KWD_POOL2_ADDRESS\",code:\"`./getimage.sh FromGiver.tvc`\"" --signer keys1

everdev contract run PseudoFund -a $BLANK_ADDRESS killFund --input "address_to:\"$MY_ADDRESS\"" --signer keys1
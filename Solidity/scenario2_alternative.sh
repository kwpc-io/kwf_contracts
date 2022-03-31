#!/bin/bash

# script requires some python packages before running:
# python3 -m venv .venv
# source .venv/bin/activate
# pip install ton-client-py
# pip install aiohttp


#finalize all contracts

echo '{"fund_address_": "'$BLANK_ADDRESS'"}' > filters.json
KWDPools=$(python3 ../off-chain/fetch.py ../Solidity/KWDPool.tvc ../Solidity/KWDPool.abi.json filters.json)
FromGivers=$(python3 ../off-chain/fetch.py ../Solidity/FromGiver.tvc ../Solidity/FromGiver.abi.json filters.json)

for addr in $KWDPools $FromGivers
do
    everdev contract run Blank -a $BLANK_ADDRESS finalize --input "addr:\"$addr\"" --signer keys1
done

#topup
RESPAWN_SUMMA=50000000000
everdev contract topup Blank -a $BLANK_ADDRESS --signer keys1 --value $RESPAWN_SUMMA --signer keys1

#setCode
everdev contract run Blank -a $BLANK_ADDRESS setFundCode --input "code:\"`./getimage.sh PseudoFund.tvc`\"" --signer keys1


#get Funds
for addr in $KWDPools $FromGivers
do
    everdev contract run PseudoFund -a $BLANK_ADDRESS getFunds --input "kwdp_address:\"$addr\"" --signer keys1
done

#!/bin/bash

# deploy the Blank
DELTA_LOCK=$((7*60))
DELTA_UNLOCK=$((15*24*60*60))
NOW=`date +%s`
LOCK_TIME=$(($NOW+$DELTA_LOCK))
UNLOCK_TIME=$(($NOW+$DELTA_UNLOCK))
FARM_RATE=80
KWF_LOCK_TIME=180
QUANT=10000000000
MIN_SUMMA=18000000000
MAX_SUMMA=180000000000
BLANK_DEPLOY_FEE=21000000000
# VOTING_TIME=$((4*60))

#deploy Blank
./blank_deploy.sh $LOCK_TIME $UNLOCK_TIME $FARM_RATE $KWF_LOCK_TIME $QUANT 1 $MIN_SUMMA $MAX_SUMMA $BLANK_DEPLOY_FEE | tee blank_deploy.log
GREP_STR1="Contract is deployed at address:"
export BLANK_ADDRESS=`grep "$GREP_STR1" blank_deploy.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#set FromGiver code hash
./blank_setFromGiverCode.sh $BLANK_ADDRESS
#set KWD pool code hash
./blank_setKWDPoolCode.sh $BLANK_ADDRESS

export MY_ADDRESS=0:`everdev network info | grep devnet | sed -e "s/.*0: *//"`
#"0:f610781c68e380a9b49ca7ca0c211673ad18f8237c187eed27a17f40b8267438"

GIVER1_ADDRESS=$MY_ADDRESS
#deploy giver1
./blank_deployFG.sh $BLANK_ADDRESS $GIVER1_ADDRESS 1 | tee blank_deployFG1.log
GREP_STR2="\"value0\":"
export FROM_GIVER1_ADDRESS=`grep "$GREP_STR2" blank_deployFG1.log | sed -e "s/ *$GREP_STR2  *//" | tr -d '\n' | sed 's/\"//g'`

KWD_DEPLOY_FEE=6000000000
#deploy kwd pool1
FINAL_ADDRESS1=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 1 $FINAL_ADDRESS1  $KWD_DEPLOY_FEE | tee kwdpool_deploy1.log
export KWD_POOL1_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy1.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool2
FINAL_ADDRESS2=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 2 $FINAL_ADDRESS2  $KWD_DEPLOY_FEE | tee kwdpool_deploy2.log
export KWD_POOL2_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy2.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool3
FINAL_ADDRESS3=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 3 $FINAL_ADDRESS3  $KWD_DEPLOY_FEE | tee kwdpool_deploy3.log
export KWD_POOL3_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy3.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool4
FINAL_ADDRESS4=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 4 $FINAL_ADDRESS4  $KWD_DEPLOY_FEE | tee kwdpool_deploy4.log
export KWD_POOL4_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy4.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool5
FINAL_ADDRESS5=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 5 $FINAL_ADDRESS5  $KWD_DEPLOY_FEE | tee kwdpool_deploy5.log
export KWD_POOL5_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy5.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool6
FINAL_ADDRESS6=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 6 $FINAL_ADDRESS6  $KWD_DEPLOY_FEE | tee kwdpool_deploy6.log
export KWD_POOL6_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy6.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool7
FINAL_ADDRESS7=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS 7 $FINAL_ADDRESS7  $KWD_DEPLOY_FEE | tee kwdpool_deploy7.log
export KWD_POOL7_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy7.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`


KWD_SUMMA=11000000000
#top up kwd1
everdev contract topup KWDPool -a $KWD_POOL1_ADDRESS --signer keys1 --value $KWD_SUMMA

#top up kwd2
everdev contract topup KWDPool -a $KWD_POOL2_ADDRESS --signer keys1 --value $KWD_SUMMA

#top up kwd3
everdev contract topup KWDPool -a $KWD_POOL3_ADDRESS --signer keys1 --value $KWD_SUMMA

#top up kwd4
everdev contract topup KWDPool -a $KWD_POOL4_ADDRESS --signer keys1 --value $KWD_SUMMA
#top up kwd5
everdev contract topup KWDPool -a $KWD_POOL5_ADDRESS --signer keys1 --value $KWD_SUMMA
#top up kwd6
everdev contract topup KWDPool -a $KWD_POOL6_ADDRESS --signer keys1 --value $KWD_SUMMA
#top up kwd7
everdev contract topup KWDPool -a $KWD_POOL7_ADDRESS --signer keys1 --value $KWD_SUMMA



GIVER_SUMMA=50000000000
#top up giver
everdev contract topup FromGiver -a $FROM_GIVER1_ADDRESS --signer keys1 --value $GIVER_SUMMA

#topup
RESPAWN_SUMMA=50000000000
everdev contract topup Blank -a $BLANK_ADDRESS --signer keys1 --value $RESPAWN_SUMMA --signer keys1

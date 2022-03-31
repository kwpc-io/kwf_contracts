#!/bin/bash

# deploy the Blank
DELTA_LOCK=$((10*60))
DELTA_UNLOCK=$((600*60))
NOW=`date +%s`
LOCK_TIME=$(($NOW+$DELTA_LOCK))
UNLOCK_TIME=$(($NOW+$DELTA_UNLOCK))
FARM_RATE1=80
FARM_RATE2=50
KWF_LOCK_TIME=180
QUANT=10000000000
MIN_SUMMA=18000000000
MAX_SUMMA=180000000000
BLANK_DEPLOY_FEE=21000000000

#deploy Blank1
./blank_deploy.sh $LOCK_TIME $UNLOCK_TIME $FARM_RATE1 $KWF_LOCK_TIME $QUANT 1 $MIN_SUMMA $MAX_SUMMA $BLANK_DEPLOY_FEE | tee blank_deploy1.log
GREP_STR1="Contract is deployed at address:"
export BLANK_ADDRESS1=`grep "$GREP_STR1" blank_deploy1.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy Blank2
./blank_deploy.sh $LOCK_TIME $UNLOCK_TIME $FARM_RATE2 $KWF_LOCK_TIME $QUANT 2 $MIN_SUMMA $MAX_SUMMA $BLANK_DEPLOY_FEE | tee blank_deploy2.log
GREP_STR1="Contract is deployed at address:"
export BLANK_ADDRESS2=`grep "$GREP_STR1" blank_deploy2.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`


#set FromGiver code hash for Blank1
./blank_setFromGiverCode.sh $BLANK_ADDRESS1
#set FromGiver code hash for Blank2
./blank_setFromGiverCode.sh $BLANK_ADDRESS2
#set KWD pool code hash for Blank1
./blank_setKWDPoolCode.sh $BLANK_ADDRESS1
#set KWD pool code hash for Blank1
./blank_setKWDPoolCode.sh $BLANK_ADDRESS2

MY_ADDRESS=0:`everdev network info | grep devnet | sed -e "s/.*0: *//"`
#"0:f610781c68e380a9b49ca7ca0c211673ad18f8237c187eed27a17f40b8267438"

GIVER1_1_ADDRESS=$MY_ADDRESS
#deploy giver1 for Blank1
./blank_deployFG.sh $BLANK_ADDRESS1 $GIVER1_1_ADDRESS 1 | tee blank_deployFG1_1.log
GREP_STR2="\"value0\":"
export FROM_GIVER1_1_ADDRESS=`grep "$GREP_STR2" blank_deployFG1_1.log | sed -e "s/ *$GREP_STR2  *//" | tr -d '\n' | sed 's/\"//g'`
GIVER2_1_ADDRESS=$MY_ADDRESS
#deploy giver2 for Blank1
./blank_deployFG.sh $BLANK_ADDRESS1 $GIVER2_1_ADDRESS 2 | tee blank_deployFG2_1.log
GREP_STR2="\"value0\":"
export FROM_GIVER2_1_ADDRESS=`grep "$GREP_STR2" blank_deployFG2_1.log | sed -e "s/ *$GREP_STR2  *//" | tr -d '\n' | sed 's/\"//g'`
GIVER1_2_ADDRESS=$MY_ADDRESS
#deploy giver1 for Blank2
./blank_deployFG.sh $BLANK_ADDRESS2 $GIVER1_2_ADDRESS 1 | tee blank_deployFG1_2.log
GREP_STR2="\"value0\":"
export FROM_GIVER1_2_ADDRESS=`grep "$GREP_STR2" blank_deployFG1_2.log | sed -e "s/ *$GREP_STR2  *//" | tr -d '\n' | sed 's/\"//g'`
GIVER2_2_ADDRESS=$MY_ADDRESS
#deploy giver2 for Blank1
./blank_deployFG.sh $BLANK_ADDRESS2 $GIVER2_2_ADDRESS 2 | tee blank_deployFG2_2.log
GREP_STR2="\"value0\":"
export FROM_GIVER2_2_ADDRESS=`grep "$GREP_STR2" blank_deployFG2_2.log | sed -e "s/ *$GREP_STR2  *//" | tr -d '\n' | sed 's/\"//g'`

KWD_DEPLOY_FEE=6000000000
#deploy kwd pool1 for Blank1
FINAL_ADDRESS1_1=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS1 1 $FINAL_ADDRESS1_1  $KWD_DEPLOY_FEE | tee kwdpool_deploy1_1.log
export KWD_POOL1_1_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy1_1.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool2 for Blank1
FINAL_ADDRESS2_1=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS1 2 $FINAL_ADDRESS2_1  $KWD_DEPLOY_FEE | tee kwdpool_deploy2_1.log
export KWD_POOL2_1_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy2_1.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool3 for Blank1  (initialize no balance)
FINAL_ADDRESS3_1=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS1 3 $FINAL_ADDRESS3_1  $KWD_DEPLOY_FEE | tee kwdpool_deploy3_1.log
export KWD_POOL3_1_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy3_1.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool1 for Blank2
FINAL_ADDRESS1_2=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS2 1 $FINAL_ADDRESS1_2  $KWD_DEPLOY_FEE | tee kwdpool_deploy1_2.log
export KWD_POOL1_2_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy1_2.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool2 for Blank2
FINAL_ADDRESS2_2=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS2 2 $FINAL_ADDRESS2_2  $KWD_DEPLOY_FEE | tee kwdpool_deploy2_2.log
export KWD_POOL2_2_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy2_2.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

#deploy kwd pool3 for Blank1  (initialize no balance)
FINAL_ADDRESS3_2=$MY_ADDRESS
./kwdpool_deploy.sh $BLANK_ADDRESS2 3 $FINAL_ADDRESS3_2  $KWD_DEPLOY_FEE | tee kwdpool_deploy3_2.log
export KWD_POOL3_2_ADDRESS=`grep "$GREP_STR1" kwdpool_deploy3_2.log | sed -e "s/ *$GREP_STR1  *//" | tr -d '\n'`

GIVER_SUMMA=20000000000
#top up giver1 for Blank1
everdev contract topup FromGiver -a $FROM_GIVER1_1_ADDRESS --signer keys1 --value $GIVER_SUMMA
#top up giver2 for Blank1
everdev contract topup FromGiver -a $FROM_GIVER2_1_ADDRESS --signer keys1 --value $GIVER_SUMMA
#top up giver1 for Blank2
everdev contract topup FromGiver -a $FROM_GIVER1_2_ADDRESS --signer keys1 --value $GIVER_SUMMA
#no top up giver2 for Blank2


KWD_SUMMA=11000000000
#top up kwd1 for Blank1
everdev contract topup KWDPool -a $KWD_POOL1_1_ADDRESS --signer keys1 --value $KWD_SUMMA

#top up kwd2 for Blank1
everdev contract topup KWDPool -a $KWD_POOL2_1_ADDRESS --signer keys1 --value $KWD_SUMMA

#top up kwd1 for Blank2
everdev contract topup KWDPool -a $KWD_POOL1_2_ADDRESS --signer keys1 --value $KWD_SUMMA

#top up kwd1 for Blank2
everdev contract topup KWDPool -a $KWD_POOL2_2_ADDRESS --signer keys1 --value $KWD_SUMMA


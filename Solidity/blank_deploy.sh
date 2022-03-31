#!/bin/bash

#uint256 static lock_time_;
#uint256 static unlock_time_;
#uint8   static farm_rate_ ; 
#uint256 static kwf_lock_time_ ;  
#uint128 static quant_ ;

everdev contract deploy Blank --data "lock_time_:$1,unlock_time_:$2,farm_rate_:$3,kwf_lock_time_:$4,quant_:$5,nonce_:$6" --input "min_summa:$7,max_summa:$8" --signer keys1 -v $9

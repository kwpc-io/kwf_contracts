
pragma ton-solidity ^0.53.0;

import "IBlank.sol";

contract KWDPool {


uint128 constant MIN_VALUE = 100000;
uint8 constant MINIMUM_GAS_FOR_COMPUTE = 5;
uint8 constant DEFAULT_MSG_FLAGS = 0;

    uint256 deployer_pubkey_ ;      
    uint128 balance_ ;
    address acc_address_ ;            
    address fund_address_   ;         
    uint256 lock_time_ ;              
    uint256 unlock_time_ ;            
    address final_address_ ;          
    uint128 min_balance_ ;            
    uint128 epsilon_    ;             
    uint128 quant_   ;                
    bool balance_flag_ ;          
    bool fund_ready_flag_ ;        

constructor (address fund_address) public 
{
   require (msg.pubkey() != 0 , 2);
   require (tvm.pubkey() == msg.pubkey() , 2);
   require (address(this).balance >= min_balance_ , 2);
   require (now < lock_time_ , 2);
   tvm.accept();
   fund_address_ = fund_address;
   balance_ = 0;
   balance_flag_ = false; 
   fund_ready_flag_ = false; 
}

receive () external
{
   if (balance_ == 0) {
          require (now < lock_time_ , 2);
        }
   else {
          tvm.accept();
          if(!balance_flag_) {
IBlank(fund_address_).notifyRight{flag:MINIMUM_GAS_FOR_COMPUTE} (balance_ , fund_address_) ; 
                 balance_flag_ = true ; 
          }
   }
}


function notifyParticipant(uint128 summa_investors , uint128 summa_givers) public
{
   require (msg.sender == fund_address_ , 2);
   require ((now >= lock_time_) && (now <= unlock_time_) , 2);
   tvm.accept();
   fund_ready_flag_ = true;
   if (summa_investors < summa_givers) {
     address(this).transfer((balance_ * summa_givers) / summa_investors , true , DEFAULT_MSG_FLAGS);
        } 
}

}




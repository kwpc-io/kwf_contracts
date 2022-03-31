
pragma ton-solidity >=0.53.0;

import "IBlank.sol";

contract KWDPool {


uint128 constant MIN_VALUE = 100000;
uint8 constant MINIMUM_GAS_FOR_COMPUTE = 5;
uint8 constant DEFAULT_MSG_FLAGS = 0;

uint128 balance_ ;
address fund_address_ ;
uint256 lock_time_ ;
uint256 unlock_time_ ;
optional (address) final_address_ ; 
uint128 min_balance_ ;
uint128 epsilon_ ;
uint128 quant_ ;
bool voiting_flag_ ;
bool balance_flag_ ;
bool fund_ready_flag_ ;

constructor (address fund_address , uint128 quant , optional (address) final_address) public {
   require ( msg.pubkey() != 0 , 2);
   require ( msg.pubkey() == tvm.pubkey()  , 2);
   require(address(this).balance >= min_balance_ , 2);
   require ( now < lock_time_ , 2);
   tvm.accept();
   fund_address_ = fund_address;
   quant_ = quant;
   balance_ = 0 ;
   final_address_ = final_address;
   voiting_flag_ = false; 
   balance_flag_ = false; 
   fund_ready_flag_ = false; 
}

receive ()  external 
{
  if(balance_ == 0) {
          tvm.rawReserve (quant_ + MIN_VALUE , 2 );
          require ( msg.value >= quant_ + epsilon_ , 2);
  } else {
          require (now < lock_time_ , 2);
  } 
   tvm.accept();
   if(!balance_flag_) {
   IBlank(fund_address_).notifyLeft{flag:MINIMUM_GAS_FOR_COMPUTE} (balance_ , quant_) ;
             balance_flag_ = true ;
         }
 }


function notifyParticipant (uint128 summa_investors, uint128 summa_givers) public 
{
   require ( msg.sender == fund_address_ , 2);
   require ((now >= lock_time_) &&
              (now <= unlock_time_) , 2);
   tvm.accept();
   fund_ready_flag_ = true;
   if (summa_investors > summa_givers) {
      if(final_address_.hasValue() ) {
                (final_address_.get()).transfer ( (balance_ * summa_investors) /
                                      summa_givers , true , DEFAULT_MSG_FLAGS);
      }
      else {
               address(this).transfer ( (balance_ * summa_investors) /
               summa_givers , true , DEFAULT_MSG_FLAGS );
      }
   }
}

function setFinalAddress (address final_address)  public 
{
require ((tvm.pubkey() == msg.pubkey()) , 2);
//   require (final_address != 0 , 0);
   require ((address(this).balance >= balance_ + epsilon_) , 2);
   tvm.accept();
   final_address_.set(final_address) ; 
}

}



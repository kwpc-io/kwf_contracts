
pragma ton-solidity >=0.54.0;
pragma AbiHeader time; 
pragma AbiHeader expire; 
pragma AbiHeader pubkey;

import "IBlank.sol";
// import "IKWFundParticipant.sol";

/*struct VarInit { 
      address fund_address;
      uint256 lock_time;
      uint256 unlock_time;
      uint128 quant;
      uint128 farm_rate ;
}*/

contract DKWDPool is IKWFundParticipant { 

uint128 constant MIN_BALANCE = 5 ton ;
uint128 constant EPSILON_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_PARTICIPANT_MESSAGE = 1 ton ;
uint128 constant RESPAWN_BALANCE = 5 ;
uint128 constant FG_MIN_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_FUND_MESSAGE = 0.5 ton ;

uint16 constant ALL_BALANCE_MSG_FLAG = 128 ;
uint16 constant DEFAULT_MSG_FLAGS = 0 ;
uint16 constant ALL_BALANCE_BUT_FEE_FLAGS = 64 ;

uint16 constant error_not_external_message = 100 ;
uint16 constant error_not_my_pubkey = 101 ;
uint16 constant error_balance_too_low = 102 ;
uint16 constant error_time_too_late = 103 ;
uint16 constant error_quant_not_set = 104 ;
uint16 constant error_farm_rate_not_set = 105 ;
uint16 constant error_msg_value_too_low = 106 ;
uint16 constant error_not_my_fund = 107 ;
uint16 constant error_time_not_inside = 108 ;
uint16 constant error_fund_ready_set = 109 ;
uint16 constant error_final_address_not_set = 110 ;
uint16 constant error_balance_not_positive = 111 ;
uint16 constant error_fund_ready_not_set = 112 ;
uint16 constant error_time_too_early = 113 ;
uint16 constant error_not_initialized = 114 ;
uint16 constant error_initialized = 115 ;
uint16 constant error_fund_not_set = 116 ;

      uint128 balance_;
      address static fund_address_;
      uint256 static lock_time_;
      uint256 static unlock_time_;
      optional(address) final_address_;
      uint128 static quant_;
      bool voting_flag_;
      bool fund_ready_flag_;
      uint8 static farm_rate_ ;
      bool initialized_ ;

modifier check_owner {
  require ( msg.pubkey () != 0, error_not_external_message );
  require ( tvm.pubkey () == msg.pubkey (), error_not_my_pubkey );
  _ ;
}
 
modifier check_init {
  require ( initialized_, error_not_initialized) ;
  _ ;
}

modifier check_fund {
  require ( msg.sender == fund_address_, error_not_my_fund) ;
  _ ;
}

constructor (optional (address) final_address) public check_owner
{
   require (address(this).balance >= MIN_BALANCE + GAS_FOR_FUND_MESSAGE , error_balance_too_low);
   require (now < lock_time_ , error_time_too_late);
   require ( quant_ > 0 , error_quant_not_set );
   require ( farm_rate_  > 0 , error_farm_rate_not_set ) ;
   require ( fund_address_ != address(0) , error_fund_not_set );

   tvm.accept();
   IBlank(fund_address_).isFundReady{value:GAS_FOR_FUND_MESSAGE}(tvm.pubkey(), quant_, farm_rate_);
   balance_ = 0;
   final_address_ = final_address;
   voting_flag_ = false; 
   fund_ready_flag_ = false; 
   initialized_ = false ;
}

function initialize () external override check_fund
{ 
  require (! initialized_ , error_initialized) ;
  tvm.accept () ; 
  
  initialized_ = true ; 
}  

receive() external check_init
{
    if (balance_ == 0) {
       require (msg.value >= quant_ , error_msg_value_too_low);
       require (address(this).balance >=
                  msg.value + GAS_FOR_FUND_MESSAGE + EPSILON_BALANCE , error_balance_too_low);
       require (now < lock_time_ , error_time_too_late);
       tvm.accept();
       balance_ = quant_;
       IBlank (fund_address_).notifyLeft{value:GAS_FOR_FUND_MESSAGE} 
            ( msg.pubkey() , quant_ , farm_rate_ , (balance_ * farm_rate_) / 100 ) ;
       if (! final_address_.hasValue() ) 
       {
          final_address_.set(msg.sender);
          uint128 extra = (msg.value - quant_);
          if (extra >= EPSILON_BALANCE) 
          {
               address(msg.sender).transfer ( extra , false , 0);
          } 
       }
    }
}

function notifyParticipant(uint128 summa_investors , uint128 summa_givers) external override check_init check_fund
{
   require ((now >= lock_time_) && now <= unlock_time_ , error_time_not_inside);
   require (! fund_ready_flag_ , error_fund_ready_set);
   require (final_address_.hasValue() , error_final_address_not_set);
   require ((balance_ > 0) , error_balance_not_positive);
   require ((address(this).balance >= msg.value + balance_ + EPSILON_BALANCE) , error_balance_too_low);
   tvm.accept();
   fund_ready_flag_ = true;
   if (summa_investors > summa_givers) 
   {
     uint128 extra = balance_ * (summa_investors - summa_givers ) / summa_investors ;
     balance_ -= extra ;
     address(final_address_.get()).transfer (extra , true , DEFAULT_MSG_FLAGS);
   }
   IBlank (fund_address_).acknowledgeFinalizeLeft{value:0,flag:ALL_BALANCE_BUT_FEE_FLAGS} (quant_ , msg.pubkey() , farm_rate_) ;
}

function setFinalAddress (address final_address) external check_init check_owner
{
    require (address(this).balance >= balance_ + EPSILON_BALANCE , error_balance_too_low); 
   tvm.accept(); 
   final_address_.set(final_address) ; 
}

function _sendFunds (address address_to) internal
{ 
  if ( balance_ > 0 ) {
   address(address_to).transfer( balance_ , false , DEFAULT_MSG_FLAGS ) ; 
  }
  selfdestruct ( final_address_.get() ) ; 
}

function sendFunds (address address_to) external check_init  check_fund
{
  require ( fund_ready_flag_ , error_fund_ready_not_set); 
  require ( final_address_.hasValue() , error_final_address_not_set) ;

  require ( address(this).balance >= msg.value + balance_ + EPSILON_BALANCE, error_balance_too_low) ;
  tvm.accept () ; 
  _sendFunds (address_to) ; 
}

function returnFunds (/*uint128 sum ,*/ address address_to) external check_owner
{ 
  require ((now > unlock_time_) || (! initialized_) , error_time_too_early) ; 
  require ( address(this).balance >= EPSILON_BALANCE, error_balance_too_low) ; 
  tvm.accept () ; 
  final_address_.set(address_to) ; 
  _sendFunds ( address_to ) ;  
} 


}
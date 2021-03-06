
pragma ton-solidity >=0.54.0;
pragma AbiHeader time; 
pragma AbiHeader expire; 
//pragma AbiHeader pubkey;

import "IBlank.sol";
import "IKWFundParticipant.sol";
<<<<<<< HEAD
=======

>>>>>>> 2b696b229d23fd8db25d66b8fc12902960bb7d60

/*struct VarInit { 
      address fund_address_;
      uint256 lock_time_;
      uint256 unlock_time_;
      address giver_address_;
 } */

 contract DFromGiver is IKWFundParticipant { 

uint128 constant MIN_BALANCE = 5 ton ;
uint128 constant EPSILON_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_PARTICIPANT_MESSAGE = 1 ton ;
uint128 constant RESPAWN_BALANCE = 5 ;
uint128 constant FG_MIN_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_FUND_MESSAGE = 0.5 ton ;

uint16 constant ALL_BALANCE_MSG_FLAG = 128 ;
uint16 constant DEFAULT_MSG_FLAGS = 0 ;
uint16 constant MSG_VALUE_BUT_FEE_FLAGS = 64 ;


uint16 constant not_external_message = 100 ;
uint16 constant not_my_pubkey = 101 ;
uint16 constant balance_too_low = 102 ;
uint16 constant time_too_late = 103 ;
uint16 constant quant_not_set = 104 ;
uint16 constant farm_rate_not_set = 105 ;
uint16 constant msg_value_too_low = 106 ;
uint16 constant not_my_fund = 107 ;
uint16 constant time_not_inside = 108 ;
uint16 constant fund_ready_set = 109 ;
uint16 constant final_address_not_set = 110 ;
uint16 constant balance_not_positive = 111 ;
uint16 constant fund_ready_not_set = 112 ;
uint16 constant time_too_early = 113 ;
uint16 constant not_initialized = 114 ;
uint16 constant initialized = 115 ;
uint16 constant fund_not_set = 116 ;
uint16 constant not_internal_message = 117 ;
uint16 constant cant_initialize = 118 ;
uint16 constant not_my_giver = 119 ;


      uint128 balance_;
      address static fund_address_;
      uint256 static lock_time_;
      uint256 static unlock_time_;
      address static giver_address_;
      bool fund_ready_flag_;
 
constructor() public
{
   require (msg.sender != address(0) , not_internal_message);
   require (msg.sender == fund_address_ , not_my_fund);
//   require (address(this).value >= MIN_BALANCE + EPSILON_BALANCE , 2);
//   require (giver_address_ != address(0) , 2);
//   require (now < lock_time_ , 2);
   balance_ = 0;
   fund_ready_flag_ = false; 
}

function initialize (/*bool ok*/) external pure
{
// ?? ?????????? ?????????? ???????????????
  require (false, cant_initialize) ;
}


receive() external
{
   if (address(this).value > MIN_BALANCE) {
      require (msg.sender == giver_address_ , not_my_giver);
      require (now < lock_time_ , time_too_late);
      require (address(this).balance > msg.value + 
                                       balance_ + 
                                       GAS_FOR_FUND_MESSAGE + 
                                       EPSILON_BALANCE, balance_too_low);
      tvm.accept();
      IBlank (fund_address_).notifyRight{value: GAS_FOR_FUND_MESSAGE}(balance_ , msg.value , giver_address_) ;
      balance_ += address(this).balance ;
    }
}

function notifyParticipant (uint128 summa_investors , uint128 summa_givers) external
{
   require (msg.sender == fund_address_ , not_my_giver);
   require ((now >= lock_time_) && now <= unlock_time_ , time_not_inside);
   require (! fund_ready_flag_ , fund_ready_set);
   require (balance_ > 0 , 2);
   require (address(this).balance >= msg.value + 
                                     balance_ + 
                                     EPSILON_BALANCE , balance_too_low);
   tvm.accept();
   fund_ready_flag_ = true;
   if (summa_givers > summa_investors) 
   {
      uint128 extra = balance_ * ( summa_givers - summa_investors ) / summa_givers ; 
      balance_ -= extra;
      address(giver_address_).transfer ( extra , true , DEFAULT_MSG_FLAGS);
   }
   IBlank (fund_address_).acknowledgeFinalizeRight{value:0,flag:MSG_VALUE_BUT_FEE_FLAGS}(giver_address_) ;
}

function _sendFunds (address address_to) private 
{ 
  if ( balance_ > 0 ) 
  { 
      address(address_to).transfer ( balance_ , false , DEFAULT_MSG_FLAGS ) ;
  } 
  selfdestruct ( giver_address_  ) ; 
} 


function sendFunds (address address_to) external
{
  require ( msg.sender == fund_address_, not_my_fund) ; 
  require ( fund_ready_flag_ , fund_ready_not_set) ; 
//  require ( now > unlock_time_ , 2) ; 
  require ( address(this).balance >= address(this).value + balance_ + EPSILON_BALANCE, balance_too_low) ; 
  tvm.accept () ; 
  _sendFunds (address_to) ; 
} 

function returnFunds() public 
{
  require (now > unlock_time_ , time_too_early) ; 
  require ( address(this).balance >= EPSILON_BALANCE, balance_too_low) ; 
  tvm.accept () ; 
  _sendFunds ( giver_address_ ) ; 
} 

}

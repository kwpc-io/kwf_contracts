pragma ton-solidity >=0.54.0;
pragma AbiHeader time; 
pragma AbiHeader expire; 
pragma AbiHeader pubkey;

import "IBlank.sol";
import "IKWFund.sol";
import "IKWFundParticipant.sol";
import "KWErrorConstants.sol";
import "KWMessagesConstants.sol";


contract DFromGiver is IKWFundParticipant { 

uint128 balance_;
address static fund_address_;
uint32 lock_time_;
uint32 unlock_time_;
address static giver_address_;
bool fund_ready_flag_;
uint256 static nonce_;

modifier check_fund {
  require ( msg.sender == fund_address_, KWErrors.error_not_my_fund) ;
  _ ;
}
 
constructor(uint32 lock_time, uint32 unlock_time) public check_fund
{
  require ( !fund_address_.isStdZero() , KWErrors.error_not_internal_message );
  require ( now < lock_time , KWErrors.error_time_too_late );
  require ( lock_time < unlock_time , KWErrors.error_unlock_time_less_lock ); 
  tvm.accept () ; 

  balance_ = 0 ;
  fund_ready_flag_ = false ; 
  lock_time_ = lock_time;
  unlock_time_  = unlock_time;

  IBlank(fund_address_).acknowledgeDeploy
                        {value:KWMessages.GAS_FOR_FUND_MESSAGE , 
                         flag:1} ( giver_address_ , nonce_) ;
}

function initialize (uint32 /* lock_time */, 
                     uint32 /* unlock_time */, 
                     uint128 /* quant */,
                     uint8 /* rate */,
                     uint32 /* kwf_lock_time */) external override 
{
  revert (KWErrors.error_cant_initialize) ;
}

receive() external 
{
   if (msg.value > KWMessages.FG_MIN_BALANCE) {
      require (msg.sender == giver_address_ , KWErrors.error_not_my_giver);
      require (now < lock_time_ , KWErrors.error_time_too_late);
      require (address(this).balance > msg.value + 
                                       balance_ + 
                                       KWMessages.GAS_FOR_FUND_MESSAGE + 
                                       KWMessages.EPSILON_BALANCE, KWErrors.error_balance_too_low);
      tvm.accept();
      IBlank (fund_address_).notifyRight{value: KWMessages.GAS_FOR_FUND_MESSAGE, flag:1}(giver_address_,nonce_,balance_, msg.value ) ;
      balance_ += msg.value ;
    }
}

function notifyParticipant (bool giveup, uint128 investors_adj_summa_ , uint128 summa_givers) external override check_fund
{
   require ((now >= lock_time_) && now <= unlock_time_ , KWErrors.error_time_not_inside);
   require (! fund_ready_flag_ , KWErrors.error_fund_ready_set);
   require (address(this).balance >= msg.value + 
                                     balance_ + 
                                     KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
   tvm.accept();
   bool dead_giver = (giveup || (balance_ == 0) );
   IBlank (fund_address_).acknowledgeFinalizeRight{value: msg.value ,flag:1}(giver_address_, nonce_, dead_giver) ;

   if (dead_giver ) {
      _sendFunds (giver_address_);
   } else {
      fund_ready_flag_ = true;
      if (summa_givers > investors_adj_summa_) 
      {
          uint128 extra = math.muldiv(balance_ ,  summa_givers - investors_adj_summa_  , summa_givers) ; 
          balance_ -= extra;
          giver_address_.transfer ( extra , true , 1);
/*           if (balance_ == 0) {
            selfdestruct ( fund_address_ ) ; 
          }
 */      }
   }
}

function _sendFunds (address address_to) internal 
{ 
  if ( balance_ > 0 ) 
  { 
      address_to.transfer ( balance_ , true , 1 ) ;
  } 
  selfdestruct ( fund_address_  ) ; //destruct rest to Blank as we have been deployed by it
} 


function packParams () internal view returns (TvmCell) 
{
  TvmBuilder main_builder;

  main_builder.store(fund_address_); //256+8
  main_builder.store(lock_time_); //32
  main_builder.store(unlock_time_); //32
  main_builder.store(giver_address_); //256+8
  main_builder.store(nonce_); //256
  main_builder.store(balance_); //128
  main_builder.store(fund_ready_flag_); //8

  return main_builder.toCell();
}

/* callback for sendParams */function acknowledgeFunds () external override check_fund
{
  tvm.accept();
  msg.sender.transfer (msg.value, false, 1);
  selfdestruct ( fund_address_ ) ;
}

function sendFunds (TvmCell ) external override check_fund
{
  require ( fund_ready_flag_ , KWErrors.error_fund_ready_not_set) ; 
//  require ( now > unlock_time_ , 2) ; 
  require ( address(this).balance >= msg.value +
                                     balance_  + 
                                     KWMessages.EPSILON_BALANCE, KWErrors.error_balance_too_low) ; 
  tvm.accept () ; 

  IKWFund (fund_address_).sendFromGiverParams { value:  balance_ + msg.value   , bounce: true, flag: 1 } ( giver_address_, nonce_, packParams () ) ;
  /* _sendFunds (address_to) ;  */
} 

function returnFunds() external 
{
  require (now > unlock_time_ , KWErrors.error_time_too_early) ; 
  require ( address(this).balance >= KWMessages.EPSILON_BALANCE, KWErrors.error_balance_too_low) ; 
  tvm.accept () ; 
  _sendFunds ( giver_address_ ) ; 
} 

function onVoteReject (uint8 voting_id) external override {}
function onVoteAccept () external override {}

}

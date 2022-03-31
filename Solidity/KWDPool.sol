pragma ton-solidity >=0.54.0;
pragma AbiHeader time;
pragma AbiHeader expire;
pragma AbiHeader pubkey;

import "IBlank.sol";
import "IKWFund.sol";
import "IKWFundParticipant.sol";
import "KWErrorConstants.sol";
import "KWMessagesConstants.sol";

contract DKWDPool is IKWFundParticipant {

uint128 balance_; /* virtual balance, equal to 0 or quant */
address static fund_address_;  /* address of fund */
uint32 lock_time_; /* time moment when we stop gather funds , set by Fund */
uint32 unlock_time_; /* time moment we should run the fund or funds will be unlocked , set by Fund*/
uint256 static nonce_; /* to tune the address, and determine  the keys number in deriving queue */
optional(address) final_address_; /* address to which contract is self-destructing */
uint128 quant_; /* the amount we can take from investor */
bool voting_flag_; /* unused */
bool fund_ready_flag_;  /* flag that fund is ready by both legs */
uint32 init_time_; /* time when we are initialized */
uint32 deposit_time_; /* time when deposit arrived */

uint8 farm_rate_ ; /* the rate in percents which determines the realtion between legs, set by fund */
uint32 kwf_lock_time_ ;  /* time when we can unlock kwf or duration in days, set by fund? */

bool initialized_ ; /* flag that we are initalized by Fund */

uint256 voting_bitmap_;

modifier check_owner {
  require ( msg.pubkey () != 0, KWErrors.error_not_external_message );
  require ( tvm.pubkey () == msg.pubkey (), KWErrors.error_not_my_pubkey );
  _ ;
}

modifier check_init {
  require ( initialized_, KWErrors.error_not_initialized) ;
  _ ;
}

modifier check_fund {
  require ( msg.sender == fund_address_, KWErrors.error_not_my_fund) ;
  _ ;
}

constructor (optional (address) final_address) public check_owner
{
   require ( address(this).balance >= KWMessages.KWD_MIN_BALANCE + KWMessages.GAS_FOR_FUND_MESSAGE , KWErrors.error_balance_too_low);
   /* require (now < lock_time_ , KWErrors.error_time_too_late); */
   /* require ( quant_ > 0 , KWErrors.error_quant_not_set ); */
   /* require ( farm_rate_  > 0 , KWErrors.error_farm_rate_not_set ) ; */
   require ( ! fund_address_.isStdZero() , KWErrors.error_fund_not_set );

   tvm.accept();

   IBlank(fund_address_).isFundReady{value:KWMessages.GAS_FOR_FUND_MESSAGE, flag:1}(tvm.pubkey(), nonce_);

   balance_ = 0;
   final_address_ = final_address;
   voting_flag_ = false;
   fund_ready_flag_ = false;
   initialized_ = false ;
   lock_time_ = 0 ;
   unlock_time_ = 0;
   quant_ = 0;
   farm_rate_ = 0;
   kwf_lock_time_ = 0;
   init_time_ = 0;
   deposit_time_ = 0;
   voting_bitmap_  =  0;
}

/* callback */function initialize (uint32 lock_time,
                     uint32 unlock_time,
                     uint128 quant,
                     uint8 rate,
                     uint32 kwf_lock_time) external override check_fund
{
  require ( ! initialized_ , KWErrors.error_initialized ) ;
  require ( now < lock_time , KWErrors.error_time_too_late );
  /* require ( lock_time < unlock_time , KWErrors.error_unlock_time_less_lock );
  require ( quant > 0 , KWErrors.error_quant_not_set );
  require ( rate > 0 && rate  <= 100, KWErrors.error_rate_not_set );
  require ( kwf_lock_time > 0 , KWErrors.error_kwf_lock_time_not_set ); */
  tvm.accept () ;

  quant_ = quant;
  lock_time_ = lock_time;
  unlock_time_ = unlock_time;
  farm_rate_ = rate;
  kwf_lock_time_ = kwf_lock_time;
  initialized_ = true ;
  init_time_ = now;
}

receive() external check_init
{
    if (balance_ == 0) {
       require ( msg.value >= quant_ , KWErrors.error_msg_value_too_low );
       require ( address(this).balance >= msg.value +
                                          KWMessages.GAS_FOR_FUND_MESSAGE +
                                          KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low );
       require ( now < lock_time_ , KWErrors.error_time_too_late );
       tvm.accept();

       balance_ = quant_;
       deposit_time_ = now;
       IBlank (fund_address_).notifyLeft{value:KWMessages.GAS_FOR_FUND_MESSAGE, flag:1}
            ( tvm.pubkey() , nonce_ , balance_, math.muldiv(balance_ , farm_rate_, 100) ) ;
       if (! final_address_.hasValue() )
       {
          final_address_.set(msg.sender);
       }
       uint128 extra = msg.value - quant_;
       if (extra >= KWMessages.EPSILON_BALANCE)
       {
          msg.sender.transfer ( extra , true , KWMessages.DEFAULT_MSG_FLAGS);
       }
    }
}

function notifyParticipant(bool giveup, uint128 investors_adj_summa_ , uint128 summa_givers) external override check_init check_fund
{
   require ( (now >= lock_time_) && (now <= unlock_time_) , KWErrors.error_time_not_inside);
   require (! fund_ready_flag_ , KWErrors.error_fund_ready_set);
   require ( final_address_.hasValue() , KWErrors.error_final_address_not_set);
/*    require ( balance_ > 0 , KWErrors.error_balance_not_positive);
 */   require ( address(this).balance >= msg.value +
                                      balance_ +
                                      KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
   tvm.accept();
if (balance_ == 0) {
  selfdestruct ( final_address_.get() ) ;
}
else {
   IBlank (fund_address_).acknowledgeFinalizeLeft{value: msg.value, bounce: true, flag: 1 }
    ( tvm.pubkey() , nonce_ ) ;

   if (giveup)
   {
      _sendFunds(final_address_.get());
   } else {
      fund_ready_flag_ = true;
      if (investors_adj_summa_ > summa_givers)
      {
        uint128 extra = math.muldiv(balance_ , investors_adj_summa_ - summa_givers , investors_adj_summa_ );
        balance_ -= extra ;
        final_address_.get().transfer (extra , true , 1);
      }
   }
}
}

function setFinalAddress (address final_address) external check_init check_owner
{
  require (address(this).balance >= balance_ + KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  tvm.accept();
  final_address_.set(final_address) ;
}

function _sendFunds (address address_to) internal
{
  if ( balance_ > 0 ) {
   address_to.transfer( balance_ , true , 1 ) ;
  }
  selfdestruct ( final_address_.get() ) ;
}

function packParams (TvmCell code) internal view returns (TvmCell)
{
  TvmBuilder main_builder;

  main_builder.store(lock_time_, unlock_time_, quant_, farm_rate_, kwf_lock_time_);

  TvmBuilder static_builder;
  static_builder.store(tvm.pubkey(), fund_address_, nonce_);

  TvmBuilder dyn_builder;
  dyn_builder.store(initialized_, balance_, final_address_, fund_ready_flag_, init_time_, deposit_time_);

  main_builder.storeRef(static_builder);
  main_builder.storeRef(dyn_builder);
  main_builder.storeRef(code);

  return main_builder.toCell();
}

/* callback for sendParams */function acknowledgeFunds () external override check_init check_fund
{
  tvm.accept();
  msg.sender.transfer (msg.value, false, 1);
  selfdestruct ( final_address_.get() ) ;
}



function sendFunds (TvmCell code ) external override check_init  check_fund
{
  require ( fund_ready_flag_ , KWErrors.error_fund_ready_not_set);
  require ( final_address_.hasValue() , KWErrors.error_final_address_not_set) ;
  require ( address(this).balance >= msg.value +
                                     balance_ +
                                     KWMessages.EPSILON_BALANCE, KWErrors.error_balance_too_low) ;
  tvm.accept () ;

  /* make a named call with params */
  /* balance_ = 0;  */

  IKWFund (fund_address_).sendKWDPoolParams{value: balance_ + msg.value, bounce: true, flag: 1 } (tvm.pubkey(), nonce_, packParams (code) ) ;
}

function returnFunds (/*uint128 sum ,*/ address address_to) external check_owner
{
  require (address_to != address(this), KWErrors.error_return_address_is_mine);
  require ((now > unlock_time_) || (! initialized_) , KWErrors.error_time_too_early) ;
  require ( address(this).balance >= KWMessages.EPSILON_BALANCE, KWErrors.error_balance_too_low) ;
  tvm.accept () ;

  final_address_.set(address_to) ;
  _sendFunds ( address_to ) ;
}

function returnExtraFunds (address address_to) external view check_owner
{
  tvm.accept () ;
  uint128 delta = address(this).balance - balance_ - KWMessages.KWD_MIN_BALANCE;
  if (delta > KWMessages.EPSILON_BALANCE)
  {
    address_to.transfer( delta , true , 1 ) ;
  }
}

function vote (bool choice, uint8 voting_id, uint256 code_hash) external check_init check_owner
{
  require (address(this).balance >= KWMessages.VOTING_FEE + 2*KWMessages.EPSILON_BALANCE, KWErrors.error_balance_too_low) ;
  require (voting_bitmap_ & (uint256(1) << voting_id) == 0, KWErrors.error_already_voted);
  tvm.accept();

  voting_bitmap_ |= uint256(1) << voting_id;
  IBlank(fund_address_).vote{value:KWMessages.VOTING_FEE + KWMessages.EPSILON_BALANCE, flag:1}(tvm.pubkey(), nonce_, choice, quant_, voting_id, code_hash);
}

function onVoteReject (uint8 voting_id) external override check_init check_fund
{
  voting_bitmap_ &= ~ (uint256(1) << voting_id);
}

function onVoteAccept () external override check_init check_fund
{
  return;
}

function isInitialized () public view returns(bool)
{
  return initialized_;
}

function getBalance () public view returns(uint128)
{
  return balance_;
}

function isFundReady () public view returns(bool)
{
  return fund_ready_flag_;
}

}
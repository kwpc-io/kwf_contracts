pragma ton-solidity >=0.54.0;
pragma AbiHeader time;
pragma AbiHeader expire;
pragma AbiHeader pubkey;

import "IBlank.sol";
import "IKWFundParticipant.sol";
import "KWErrorConstants.sol";
import "KWMessagesConstants.sol";

import "FromGiver.sol";
import "KWDPool.sol";

contract DBlank is IBlank {

uint256 public kwdpool_code_hash_;
uint16  public kwdpool_code_depth_;
uint256 public fromgiver_code_hash_;
uint16  public fromgiver_code_depth_;

uint128 public givers_summa_;
uint128 public investors_adj_summa_;
uint128 public investors_summa_;
uint128 public min_summa_;
uint128 public max_summa_;
//      bool    fund_ready_;
uint32  public static lock_time_;
uint32  public static unlock_time_;
uint16  public static farm_rate_ ; /* the rate in percents which determines the realtion between legs, set by fund */
uint32  public static kwf_lock_time_ ;  /* time when we can unlock kwf or duration in days, set by fund? */
uint128 public static quant_ ;
uint256 public static nonce_;

uint32 num_investors_sent_;
uint32 num_investors_received_;

bool can_change_kwdpool_code_ ;
bool can_change_fromgiver_code_ ;

uint32 num_from_givers_;

uint128 voted_for_;
uint128 voted_against_;
uint32 voting_start_time_;
uint32 voting_time_;
optional (bool) voting_result_;
uint256 voting_code_hash_;
uint8 public voting_id_;
bool public code_updated;

modifier check_owner {
  require ( msg.pubkey () != 0, KWErrors.error_not_external_message );
  require ( tvm.pubkey () == msg.pubkey (), KWErrors.error_not_my_pubkey );
  _ ;
}

function getKWDPoolAddress (uint256 pubkey , uint256 nonce) internal view returns(uint256)
{
  TvmCell dataCell = tvm.buildDataInit ( {contr:DKWDPool,
                                          pubkey:pubkey ,
                                          varInit:{
                                             fund_address_:address(this),
                                             nonce_: nonce } } );
  uint256 dataHash = tvm.hash (dataCell);
  uint16 dataDepth = dataCell.depth();
  uint256 add_std_address = tvm.stateInitHash (kwdpool_code_hash_ , dataHash , kwdpool_code_depth_, dataDepth);
  return add_std_address ;
}

modifier check_investor(uint256 pk , uint256 nonce) {
  uint256 add_std_address = msg.sender.value ;
  require (add_std_address == getKWDPoolAddress (pk , nonce) , KWErrors.error_not_my_investor ) ;
  _ ;
}

function buildFromGiverDataInitCell (address giver, uint256 nonce) internal pure returns(TvmCell)
{
    TvmCell dataCell = tvm.buildDataInit ({contr:DFromGiver,
                                 varInit:{
                                   fund_address_:address(this),
                                   giver_address_:giver ,
                                   nonce_:nonce} } );
    return dataCell;
}

function getFromGiverAddress (address giver, uint256 nonce) internal view returns(uint256)
{
  TvmCell dataCell = buildFromGiverDataInitCell (giver, nonce);
  uint256 dataHash = tvm.hash (dataCell);
  uint16 dataDepth = dataCell.depth();

  uint256 add_std_address  = tvm.stateInitHash ( fromgiver_code_hash_ , dataHash , fromgiver_code_depth_ , dataDepth );

  return add_std_address;
}

modifier check_giver(address giver, uint256 nonce) {
  uint256 add_std_address = msg.sender.value ;
  require (add_std_address == getFromGiverAddress (giver, nonce) , KWErrors.error_not_my_giver ) ;
  _ ;
}

constructor (uint128 min_summa , uint128 max_summa) public check_owner
{
  require(address(this).balance >= KWMessages.BLANK_MIN_BALANCE , KWErrors.error_balance_too_low);
  require(now < lock_time_ , KWErrors.error_time_too_late);
  require(min_summa <= max_summa , KWErrors.error_max_summa_less_min);
  require(lock_time_ /* +  KWMessages.MIN_VOTING_TIME + KWMessages.TIME_FOR_SETCODE_PREPARE + KWMessages.TIME_FOR_FUNDS_COLLECTING */  < unlock_time_ , KWErrors.error_unlock_time_less_lock );
  require(quant_ > 0 , KWErrors.error_quant_not_set );
  require(farm_rate_ > 0 && farm_rate_  <= KWMessages.MAX_FARM_RATE, KWErrors.error_rate_not_set );
  require(kwf_lock_time_ > 0 , KWErrors.error_kwf_lock_time_not_set );
  tvm.accept();

  givers_summa_ = 0;
  investors_adj_summa_ = 0;
  investors_summa_ = 0;
  min_summa_ = min_summa;
  max_summa_ = max_summa;

  fromgiver_code_hash_ = 0;
  kwdpool_code_hash_ = 0;
  fromgiver_code_depth_ = 0;
  kwdpool_code_depth_ = 0;

  num_investors_sent_ = 0;
  num_investors_received_ = 0;

  can_change_kwdpool_code_ = true ;
  can_change_fromgiver_code_ = true ;

  num_from_givers_ = 0;

  voted_for_ = 0;
  voted_against_ = 0;
  voting_start_time_ = 0;
  voting_time_ = 0;
  voting_result_.set(false);
  voting_code_hash_ = 0 ;
  voting_id_ = 0;
}

function setFromGiverCodeHash (uint256 code_hash, uint16 code_depth) external check_owner
{
   require(can_change_fromgiver_code_ , KWErrors.error_cannot_change_code );
   require(address(this).balance >= KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
   require(now < lock_time_ , KWErrors.error_time_too_late);
   tvm.accept();

   fromgiver_code_hash_ = code_hash;
   fromgiver_code_depth_ = code_depth;
}

function setKWDPoolCodeHash (uint256 code_hash, uint16 code_depth) external check_owner
{
   require(can_change_kwdpool_code_ , KWErrors.error_cannot_change_code );
   require(address(this).balance >= KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
   require(now < lock_time_ , KWErrors.error_time_too_late);
   tvm.accept();

   kwdpool_code_hash_ = code_hash;
   kwdpool_code_depth_ = code_depth;
}

function isFundReady (uint256 pk , uint256 nonce ) external override check_investor(pk , nonce)
{
  can_change_kwdpool_code_ = false ;
  IKWFundParticipant(msg.sender).initialize {value:0, bounce: true, flag:KWMessages.MSG_VALUE_BUT_FEE_FLAGS}
    (lock_time_, unlock_time_, quant_, farm_rate_, kwf_lock_time_) ;
}

function notifyLeft ( uint256 pk , uint256 nonce , uint128 balance, uint128 adj_balance) external override check_investor(pk , nonce)
{
  /* require(address(this).balance >= msg.value + KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low); */
  /* require(now < lock_time_ , KWErrors.error_time_too_late); */
  tvm.accept() ;

  investors_adj_summa_ += adj_balance ;
  investors_summa_ += balance ;
  num_investors_sent_ ++ ;
  msg.sender.transfer ( 0 , false , KWMessages.MSG_VALUE_BUT_FEE_FLAGS ) ;
}


function deployFromGiver (TvmCell code , address giver, uint256 nonce) external view check_owner returns(address)
{
  require(now < lock_time_   , KWErrors.error_time_too_late);
  require(!giver.isStdZero() , KWErrors.error_giver_not_set );
  require(tvm.hash (code) == fromgiver_code_hash_ , KWErrors.error_not_my_code );
  require(code.depth() == fromgiver_code_depth_ , KWErrors.error_not_my_code );
  require(address(this).balance >= KWMessages.FG_MIN_BALANCE +
                                   2 * KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  tvm.accept() ;

  TvmCell dataCell = buildFromGiverDataInitCell (giver, nonce);
  TvmCell stateInit = tvm.buildStateInit ( code , dataCell  ) ;

  address fgaddr = new DFromGiver {
                      value : KWMessages.FG_MIN_BALANCE + KWMessages.EPSILON_BALANCE,
                      stateInit : stateInit} (lock_time_, unlock_time_) ;

  /* require (fgaddr.value == getFromGiverAddress (giver)); */
  return fgaddr;
}

function acknowledgeDeploy (address giver, uint256 nonce) external override check_giver (giver, nonce) {
  tvm.accept () ;

  num_investors_sent_ ++ ;
  num_from_givers_    ++;
  can_change_fromgiver_code_ = false ;
}

function notifyRight (address giver , uint256 nonce, uint128 balance , uint128 income ) external override check_giver (giver, nonce)
{
  /* require(address(this).balance >= KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  require(now < lock_time_ , KWErrors.error_time_too_late);*/
  tvm.accept () ; 
  givers_summa_ += income;
        balance = balance ; /* only for warning! */
  msg.sender.transfer(0 , false , KWMessages.MSG_VALUE_BUT_FEE_FLAGS ) ;
}

function acknowledgeFinalizeLeft (uint256 pk , uint256 nonce) external override check_investor (pk , nonce)
{
  tvm.accept() ;

  num_investors_received_ ++ ;
}

function acknowledgeFinalizeRight (address giver, uint256 nonce, bool dead_giver) external override check_giver (giver, nonce)
{
  tvm.accept() ;
  if (dead_giver) { num_from_givers_ -- ; }
  num_investors_received_ ++ ;
}

function finalize (bool force_giveup, address addr) external view check_owner
{
   require (now >= lock_time_ && now + KWMessages.TIME_FOR_FUNDS_COLLECTING + KWMessages.MIN_VOTING_TIME <= unlock_time_ , KWErrors.error_time_not_inside);
   require (address(this).balance >= KWMessages.GAS_FOR_PARTICIPANT_MESSAGE + KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
   /* require ( math.min(investors_summa_ , givers_summa_) >= min_summa_ , KWErrors.error_sum_too_small); */
   require (num_investors_received_ < num_investors_sent_ , KWErrors.error_already_all_ack ) ;
   tvm.accept();

   bool giveup = math.min(investors_summa_ , givers_summa_) < min_summa_ || force_giveup;

   IKWFundParticipant(addr).notifyParticipant {value: KWMessages.GAS_FOR_PARTICIPANT_MESSAGE,
                                               bounce: true,
                                               flag: 1} (giveup, investors_adj_summa_ , givers_summa_) ;
}

function finalizeVoting () internal
{
  if (now <= voting_start_time_ + voting_time_) { return; }

  uint128 y = voted_for_;
  uint128 n = voted_against_;
  uint128 t = investors_summa_;

  voting_result_.set(y >= 1 + (t/10) + ((n*((t/2)-(t/10)))/(t/2)));

  /* if (y >= 1 + (t/10) + ((n*((t/2)-(t/10)))/(t/2)))
      { voting_result_.set(true);  }
  else
      { voting_result_.set(false); } */

  voting_id_ ++;
}


function setFundCode (TvmCell code) external check_owner
{
   require(now + KWMessages.TIME_FOR_FUNDS_COLLECTING <= unlock_time_ , KWErrors.error_time_too_late);
   require(address(this).balance >= KWMessages.RESPAWN_BALANCE , KWErrors.error_balance_too_low);
   require(tvm.hash(code) == voting_code_hash_, KWErrors.error_code_not_correct);
   tvm.accept();

   if (!voting_result_.hasValue())
   {
      finalizeVoting ();
   }
   if (!voting_result_.hasValue() || !voting_result_.get()) { return; }

   TvmBuilder main_builder;
   main_builder.store (kwdpool_code_hash_, kwdpool_code_depth_, fromgiver_code_hash_, fromgiver_code_depth_);
   //256+16+256+16

   TvmBuilder dyn_builder;
   dyn_builder.store(givers_summa_, investors_adj_summa_, investors_summa_, min_summa_, max_summa_, num_investors_sent_, num_from_givers_ );
   //128*5+32+32

   TvmBuilder static_builder;
   static_builder.store(tvm.pubkey(), lock_time_, unlock_time_, farm_rate_, kwf_lock_time_, quant_, nonce_);
   //32+32+16+32+128+256

   main_builder.storeRef(dyn_builder);
   main_builder.storeRef(static_builder);

   tvm.setcode (code);
   tvm.setCurrentCode (code);
   onCodeUpgrade (main_builder.toCell());
}

function tryEarlyComplete () internal
{
  if (!voting_result_.hasValue())
  {
    if (2 * voted_for_ > investors_summa_) { voting_result_.set(true) ; voting_id_ ++ ; } else
      if (2 * voted_against_ > investors_summa_) { voting_result_.set(false) ; voting_id_ ++ ; }
  }
}

function vote (uint256 pk , uint256 nonce, bool choice, uint128 sum, uint8 voting_id, uint256 code_hash) external override check_investor (pk , nonce)
{
  require(msg.value >= KWMessages.VOTING_FEE, KWErrors.voting_fee_too_low);

  tvm.accept();

  if ( voting_result_.hasValue() )
      { IKWFundParticipant (msg.sender).onVoteReject
                {value: 0, bounce:false, flag: 64} (voting_id) ;  return ; }

  if (now < voting_start_time_ || now > voting_start_time_ + voting_time_)
      { IKWFundParticipant (msg.sender).onVoteReject
                {value: 0, bounce:false, flag: 64} (voting_id) ;  return ; }

  if (code_hash != voting_code_hash_)
      { IKWFundParticipant (msg.sender).onVoteReject
                {value: 0, bounce:false, flag: 64} (voting_id) ;  return ; }

  if (voting_id != voting_id_)
      { IKWFundParticipant (msg.sender).onVoteReject
                {value: 0, bounce:false, flag: 64} (voting_id) ;  return ; }

  if (choice) { voted_for_     += sum ; } else
              { voted_against_ += sum ; }

  tryEarlyComplete();

  IKWFundParticipant (msg.sender).onVoteAccept
                {value: 0, bounce:false, flag: 64} () ;
}

function startVoting (uint32 voting_time, uint256 code_hash) external check_owner
{
  require(address(this).balance >= KWMessages.VOTING_FEE + KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  require(voting_time >= KWMessages.MIN_VOTING_TIME, KWErrors.voting_time_too_low);
  require(now >= lock_time_ , KWErrors.error_time_too_early);
  require(now + voting_time + 
          KWMessages.TIME_FOR_SETCODE_PREPARE + 
          KWMessages.TIME_FOR_FUNDS_COLLECTING < unlock_time_, KWErrors.voting_time_too_long);
  require(num_investors_received_ >= num_investors_sent_ , KWErrors.error_not_all_ack);
  require(voting_id_ < 255);
 /*  require(canStartNewVoting (), KWErrors.new_voting_not_allowed); */
  tvm.accept();

  if (!voting_result_.hasValue())
   {
      finalizeVoting ();
   }
  if (!voting_result_.hasValue() || voting_result_.get() == true) { return; }

  voted_for_ = 0;
  voted_against_ = 0;
  voting_start_time_ = now;
  voting_time_ = voting_time;
  voting_result_.reset();
  voting_code_hash_ = code_hash;
}


function onCodeUpgrade(TvmCell cell) private pure {
}


/* make stop-all function to return all even before unlock_time ?? */

function killBlank (address address_to) external check_owner
{
  require (address_to != address(this), KWErrors.error_return_address_is_mine);
  require (now > unlock_time_ , KWErrors.error_time_too_early);
  require (address(this).balance >= KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  tvm.accept () ;

  selfdestruct ( address_to ) ;
}

function getInvestorsSum () public view returns(uint128, uint128)
{
  return (investors_adj_summa_, investors_summa_);
}

function getGiversSum () public view returns(uint128)
{
  return givers_summa_;
}

function getInvestorsNumbers () public view returns(uint, uint)
{
  return (num_investors_sent_, num_investors_received_);
}

function getTimes () public view returns(uint256, uint256, uint256)
{
  return (lock_time_, unlock_time_, kwf_lock_time_ );
}

function getKWD_MIN_BALANCE () public pure returns(uint128)
{
  return (KWMessages.KWD_MIN_BALANCE + KWMessages.GAS_FOR_FUND_MESSAGE);
}


}
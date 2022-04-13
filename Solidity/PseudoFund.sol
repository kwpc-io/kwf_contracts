pragma ton-solidity >=0.54.0;
pragma AbiHeader time;
pragma AbiHeader expire;
pragma AbiHeader pubkey;

import "IBlank.sol";
import "IKWFund.sol";
import "IKWFundParticipant.sol";
import "KWErrorConstants.sol";
import "KWMessagesConstants.sol";

import "FromGiver.sol";
import "KWDPool.sol";


contract DPseudoFund is IKWFund {

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
  uint32  public lock_time_;
  uint32  public unlock_time_;
  uint16  public farm_rate_ ; /* the rate in percents which determines the realtion between legs, set by fund */
  uint32  public kwf_lock_time_ ;  /* time when we can unlock kwf or duration in days, set by fund? */
  uint128 public quant_ ;
  uint256 public nonce_;

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

constructor () public
{
  revert();
}

function onCodeUpgrade(TvmCell data_cell) private  {
  /* here initialize vars */

  tvm.resetStorage();

  TvmSlice s = data_cell.toSlice();

  (kwdpool_code_hash_ , kwdpool_code_depth_ , fromgiver_code_hash_ , fromgiver_code_depth_) =
    s.decode ( uint256, uint16, uint256, uint16);

  TvmSlice s1 = s.loadRefAsSlice();
  (givers_summa_, investors_adj_summa_, investors_summa_, min_summa_, max_summa_, num_investors_sent_, num_from_givers_) =
    s1.decode ( uint128, uint128, uint128, uint128, uint128, uint32, uint32) ;

  TvmSlice s2 = s.loadRefAsSlice();
  uint256 oldPubkey;
  (oldPubkey, lock_time_,    unlock_time_,    farm_rate_,    kwf_lock_time_,    quant_,    nonce_)=
      s2.decode(uint256, uint32, uint32, uint16, uint32, uint128, uint256);

  tvm.setPubkey(oldPubkey);

  code_updated = true;

}

function getFromGiverFunds (address from_giver_address ) external view check_owner
{
  require (address(this).balance >= KWMessages.GAS_FOR_PARTICIPANT_MESSAGE+KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  require (num_from_givers_ > 0 );
  /* require add check all KWDPolls */
  tvm.accept () ;
  TvmCell empty;
  IKWFundParticipant(from_giver_address).sendFunds{value:KWMessages.GAS_FOR_PARTICIPANT_MESSAGE, bounce:true, flag:1}(empty) ;
}


function transferFundsTo (address kwdp_address, TvmCell code  ) external view check_owner
{
  require (address(this).balance >= /* x*Quant*farm_rate/100  + */ KWMessages.GAS_FOR_PARTICIPANT_MESSAGE+KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  require (num_from_givers_ == 0 );
  // require ( tvm.hash (code) == kwparticipant_code_hash_ );
  /* require add check all KWDPolls */
  tvm.accept () ;

  IKWFundParticipant(kwdp_address).sendFunds{value:KWMessages.GAS_FOR_PARTICIPANT_MESSAGE, bounce:true, flag:1}(code ) ;
}

function killFund (address address_to) external check_owner
{
  require (address_to != address(this), KWErrors.error_return_address_is_mine);
  require (address(this).balance >= KWMessages.EPSILON_BALANCE , KWErrors.error_balance_too_low);
  tvm.accept () ;

  selfdestruct ( address_to ) ;
}

function sendFromGiverParams (address giver, uint256 nonce, TvmCell  /* params */ ) external override check_giver ( giver,  nonce)
{
  tvm.accept();
  IKWFundParticipant (msg.sender).acknowledgeFunds{value:KWMessages.GAS_FOR_PARTICIPANT_MESSAGE, bounce:true, flag:1}();
  num_from_givers_ --;
  /* add check all KWDPolls */
}

function sendKWDPoolParams (uint256 pk, uint256 nonce, TvmCell  /* params */ ) external override check_investor ( pk,  nonce)
{
  tvm.accept();
  IKWFundParticipant(msg.sender).acknowledgeFunds{value:KWMessages.GAS_FOR_PARTICIPANT_MESSAGE, bounce:true, flag:1}();

/* deploy KWParticipant */

}





}

pragma ton-solidity >=0.54.0;
pragma AbiHeader time; 
pragma AbiHeader expire; 
pragma AbiHeader pubkey;

import "IBlank.sol";
import "FromGiver.sol";
import "KWDPool.sol";
// import "IKWFundParticipant.sol";

contract DBlank is IBlank { 

uint128 constant MIN_BALANCE = 5 ton ;
uint128 constant EPSILON_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_PARTICIPANT_MESSAGE = 1 ton ;
uint128 constant RESPAWN_BALANCE = 5 ;
uint128 constant FG_MIN_BALANCE = 0.5 ton ;

uint16 constant ALL_BALANCE_MSG_FLAG = 128 ;
uint16 constant DEFAULT_MSG_FLAGS = 0 ;
uint16 constant ALL_BALANCE_BUT_FEE_FLAGS = 64 ;
                     uint16 constant MSG_VALUE_BUT_FEE_FLAGS = 164 ;

uint16 constant error_not_external_message = 100 ;
uint16 constant error_not_my_pubkey = 101 ;
uint16 constant error_balance_too_low = 102 ;
uint16 constant error_time_too_late = 103 ;
uint16 constant error_not_my_giver = 104 ;
uint16 constant error_not_my_code = 105 ;
uint16 constant error_msg_value_too_low = 106 ;
uint16 constant error_not_my_investor = 107 ;
uint16 constant error_time_not_inside = 108 ;
uint16 constant error_not_all_ack = 109 ;
uint16 constant error_giver_not_set = 110 ;
uint16 constant error_cannot_change_code = 111 ;
uint16 constant error_sum_too_small = 112 ;
uint16 constant error_time_too_earl = 113 ;
uint16 constant error_not_internal_message = 114 ;
uint16 constant error_unlock_time_less_lock = 115 ;

      uint256 kwdpool_code_hash_;
      uint256 fromgiver_code_hash_;
      uint128 givers_summa_;
      uint128 investors_summa_;
      uint128 min_summa_;
      uint128 max_summa_;
//      bool    fund_ready_;
      uint256 static lock_time_;
      uint256 static unlock_time_;
      uint    num_investors_sent_;
      uint    num_investors_received_;

 bool can_change_kwdpool_code_ ;
 bool can_change_fromgiver_code_ ;

modifier check_owner {
  require ( msg.pubkey () != 0, error_not_external_message );
  require ( tvm.pubkey () == msg.pubkey (), error_not_my_pubkey );
  _ ;
}

function getKWDPoolAddress (uint256 pubkey , uint128 quant , uint8 rate) internal view returns(uint256)
{
 uint256 dataHash 
  = tvm.hash (tvm.buildDataInit ( {contr:DKWDPool,
                                   pubkey:pubkey ,
                                   varInit:{
                                             fund_address_:address(this),
                                             quant_:quant ,
                                             lock_time_:lock_time_,
                                             unlock_time_:unlock_time_,
                                             farm_rate_:rate } } ));
  uint256 add_std_address 
       = tvm.stateInitHash (kwdpool_code_hash_ , dataHash , 0 , 0); 
return add_std_address ; 
}

modifier check_investor(uint256 pk , uint128 quant , uint8 rate) {
  uint256 add_std_address = address(msg.value).value ;
  require (add_std_address == getKWDPoolAddress (pk , quant , rate) , error_not_my_investor ) ;
  _ ;
}

function getFromGiverAddress (address giver) internal view returns(uint256)
{
uint256 dataHash 
  = tvm.hash (tvm.buildDataInit ({contr:DFromGiver,
                                 varInit:{
                                   fund_address_:address(this),
                                   giver_address_:giver,
                                   lock_time_:lock_time_,
                                   unlock_time_:unlock_time_ } } ));
  uint256 add_std_address 
  = tvm.stateInitHash ( fromgiver_code_hash_ , dataHash , 0 , 0); 

return add_std_address;  
}

modifier check_giver(address giver) {
  uint256 add_std_address = address(msg.value).value ;
  require (add_std_address == getFromGiverAddress (giver) , error_not_my_giver ) ;
  _ ;
}

constructor (uint128 min_summa , uint128 max_summa) public check_owner
{
   require (address(this).balance >= MIN_BALANCE , error_balance_too_low);
   require ( unlock_time_  > lock_time_ , error_unlock_time_less_lock );
   require (now < lock_time_ , error_time_too_late);
   tvm.accept();
   givers_summa_ = 0;
   investors_summa_ = 0;
   min_summa_ = min_summa;
   max_summa_ = max_summa;

fromgiver_code_hash_ = 0;
kwdpool_code_hash_ = 0;

   num_investors_sent_ = 0; 
   num_investors_received_ = 0; 

   can_change_kwdpool_code_ = true ; 
   can_change_fromgiver_code_ = true ; 
}

function setFromGiverCode (uint256 code_hash) external check_owner
{
   require ( can_change_fromgiver_code_ , error_cannot_change_code );
   require (address(this).balance >= EPSILON_BALANCE , error_balance_too_low);
   require (now < lock_time_ , error_time_too_late);
   tvm.accept(); 
   fromgiver_code_hash_ = code_hash;
}

function setKWDPoolCodeHash (uint256 code_hash) public check_owner
{
   require ( can_change_kwdpool_code_ , error_cannot_change_code );
   require (address(this).balance >= EPSILON_BALANCE , error_balance_too_low);
   require (now < lock_time_ , error_time_too_late);
   tvm.accept(); 

   kwdpool_code_hash_ = code_hash; 
}


function isFundReady (uint256 pk , uint128 quant , uint8 rate) external override check_investor(pk , quant , rate)
{
  can_change_kwdpool_code_ = false ;
  IKWFundParticipant(msg.sender).initialize {value:0,flag:ALL_BALANCE_BUT_FEE_FLAGS} ( ) ; 
}          

function notifyLeft ( uint256 pk , uint128 quant , uint8 rate , uint128 balance ) external override check_investor(pk , quant , rate)
{ 
      require ( address(this).balance >= EPSILON_BALANCE , error_balance_too_low);   
      require ( now < lock_time_ , error_time_too_late);   
      tvm.accept() ;  
      investors_summa_ += balance ; 
      num_investors_sent_ ++ ; 
      address(msg.value).transfer ( 0 , false , MSG_VALUE_BUT_FEE_FLAGS ) ;
} 


function deployFromGiver (TvmCell code , address giver) external view check_owner returns(address)
{
   require (now < lock_time_ , error_time_too_late);
   require ( giver != address(0) , error_giver_not_set );
   require ( tvm.hash (code) == fromgiver_code_hash_ , error_not_my_code );
   require (address(this).balance >= FG_MIN_BALANCE + 2 * EPSILON_BALANCE , error_balance_too_low);
   tvm.accept() ;

   TvmCell dataInit = tvm.buildDataInit ( { 
                        contr:DFromGiver, 
                        varInit: {
                                   fund_address_:address(this),
                                   giver_address_:giver,
                                   lock_time_:lock_time_,
                                   unlock_time_:unlock_time_ } } ) ;  

  TvmCell stateInit = tvm.buildStateInit ( code , dataInit , 0  ) ; 
//  can_change_fromgiver_code_ = false ; 
//  num_investors_sent_ ++ ;
  address fgaddr = new DFromGiver {
                      value:(FG_MIN_BALANCE + EPSILON_BALANCE),
                      stateInit:stateInit}() ; 

  return fgaddr;
}

function acknowledgeDeploy (address giver) external override check_giver (giver) {
  tvm.accept () ;  

  num_investors_sent_ ++ ; 
  can_change_fromgiver_code_ = false ;
}

function notifyRight (address giver , uint128 balance , uint128 income ) external override check_giver (giver)
{ 
  require ( address(this).balance >= EPSILON_BALANCE , error_balance_too_low);
  require ( now < lock_time_ , error_time_too_late);
  tvm.accept () ;
  givers_summa_ += income; 
        balance = balance ; /* only for warning! */
  address(msg.value).transfer(0 , false , MSG_VALUE_BUT_FEE_FLAGS ) ;
} 

function acknowledgeFinalizeLeft (uint128 quant , uint256 pk , uint8 rate) external override check_investor (pk , quant , rate)
{
  tvm.accept() ;

  num_investors_received_ ++ ; 
}   

function acknowledgeFinalizeRight (address giver) external override check_giver (giver)
{ 
  tvm.accept() ;

  num_investors_received_ ++ ; 
}

function finalize (address addr) external view check_owner
{
   require (now >= lock_time_ && now <= unlock_time_ , error_time_not_inside);
   require ( address(this).balance >= GAS_FOR_PARTICIPANT_MESSAGE + EPSILON_BALANCE , error_balance_too_low);
   require (math.min(investors_summa_ , givers_summa_) >= min_summa_ , error_sum_too_small);
   require ( num_investors_received_ != num_investors_sent_ , error_not_all_ack ) ;
   tvm.accept();
   IKWFundParticipant(addr).notifyParticipant{value:GAS_FOR_PARTICIPANT_MESSAGE}(investors_summa_ , givers_summa_) ; 
}

function setFundCode (TvmCell code) public view check_owner
{
   require ( num_investors_received_ == num_investors_sent_ , error_not_all_ack);
   require (now >= lock_time_ && now <= unlock_time_ , error_time_not_inside);
   require (address(this).balance >= RESPAWN_BALANCE , error_balance_too_low);
   tvm.setcode (code); 
   tvm.setCurrentCode (code); 
}

}
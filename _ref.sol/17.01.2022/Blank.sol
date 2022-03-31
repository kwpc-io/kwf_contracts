
pragma ton-solidity >=0.54.0;
pragma AbiHeader time; 
pragma AbiHeader expire; 
pragma AbiHeader pubkey;

import "IBlank.sol";
import "FromGiver.sol";
<<<<<<< HEAD
//import "KWDPool.sol";
import "IKWFundParticipant.sol";
=======
/* import "KWDPool.sol";
 */import "IKWFundParticipant.sol";
>>>>>>> 2b696b229d23fd8db25d66b8fc12902960bb7d60

contract DBlank is IBlank { 

uint128 constant MIN_BALANCE = 5 ton ;
uint128 constant EPSILON_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_PARTICIPANT_MESSAGE = 1 ton ;
uint128 constant RESPAWN_BALANCE = 5 ;
uint128 constant FG_MIN_BALANCE = 0.5 ton ;

uint16 constant ALL_BALANCE_MSG_FLAG = 128 ;
uint16 constant DEFAULT_MSG_FLAGS = 0 ;
uint16 constant MSG_VALUE_BUT_FEE_FLAGS = 64 ;

uint16 constant not_external_message = 100 ;
uint16 constant not_my_pubkey = 101 ;
uint16 constant balance_too_low = 102 ;
uint16 constant time_too_late = 103 ;
uint16 constant not_my_giver = 104 ;
uint16 constant not_my_code = 105 ;
uint16 constant msg_value_too_low = 106 ;
uint16 constant not_my_investor = 107 ;
uint16 constant time_not_inside = 108 ;
uint16 constant not_all_ack = 109 ;
uint16 constant giver_not_set = 110 ;
uint16 constant cannot_change_code = 111 ;
uint16 constant sum_too_small = 112 ;
uint16 constant time_too_earl = 113 ;
uint16 constant not_internal_message = 114 ;

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

constructor (uint128 min_summa , uint128 max_summa) public
{
   require (msg.pubkey() != 0 , not_external_message);
   require (tvm.pubkey() == msg.pubkey() , not_my_pubkey);
   require (address(this).balance >= MIN_BALANCE , balance_too_low);
   require (now < lock_time_ , time_too_late);
   tvm.accept();
   givers_summa_ = 0;
   investors_summa_ = 0;
   min_summa_ = min_summa;
   max_summa_ = max_summa;

// TODO   fromgiver_code_hash_ = 0;
// TODO   kwdpool_code_hash_ = 0;

   num_investors_sent_ = 0; 
   num_investors_received_ = 0; 

   can_change_kwdpool_code_ = true ; 
   can_change_fromgiver_code_ = true ; 
}

function setFromGiverCode (uint256 code_hash) external
{
   require (msg.pubkey() == tvm.pubkey() , not_my_pubkey);
   require ( can_change_fromgiver_code_ , cannot_change_code );
   require (address(this).balance >= EPSILON_BALANCE , balance_too_low);
   require (now < lock_time_ , time_too_late);
   tvm.accept(); 
   fromgiver_code_hash_ = code_hash;
}

function setKWDPoolCodeHash (uint256 code_hash) public
{
   require (msg.pubkey() == tvm.pubkey() , not_my_pubkey);
   require ( can_change_kwdpool_code_ , cannot_change_code );
   require (address(this).balance >= EPSILON_BALANCE , balance_too_low);
   require (now < lock_time_ , time_too_late);
   tvm.accept(); 

   kwdpool_code_hash_ = code_hash; 
}

function getKWDPoolAddress (uint256 pubkey , uint128 quant , uint128 rate) internal view returns(uint256)
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

function isFundReady (uint128 quant , uint256 pk , uint128 rate) external 
{
  uint256 add_std_address = address(msg.sender).value ;  
  require (add_std_address == getKWDPoolAddress (pk , quant , rate) , not_my_investor ) ;  
  can_change_kwdpool_code_ = false; 
  IKWFundParticipant(msg.sender).initialize {value:0,flag:MSG_VALUE_BUT_FEE_FLAGS} ( ) ; 
}          

    
function notifyLeft (uint128 balance , uint128 quant , uint256 pk , uint128 rate) external 
{ 
      uint256 add_std_address = address(msg.sender).value; // int_sender () 

      require (add_std_address == getKWDPoolAddress ( pk , quant, rate ) , not_my_investor) ;  
      require ( address(this).balance >= EPSILON_BALANCE , balance_too_low);   
      require ( now < lock_time_ , time_too_late);   
      tvm.accept() ;  
      investors_summa_ += balance ;   
      num_investors_sent_ ++ ; 
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
 
function deployFromGiver (TvmCell code , address giver) external returns(address)
{
   require (msg.pubkey() == tvm.pubkey() , not_my_pubkey);
   require (now < lock_time_ , time_too_late);
   require ( giver != address(0) , giver_not_set );
   require ( tvm.hash (code) == fromgiver_code_hash_ , not_my_code );
   require (address(this).balance >= FG_MIN_BALANCE + 2 * EPSILON_BALANCE , balance_too_low);
   tvm.accept() ;

   TvmCell dataInit = tvm.buildDataInit ( { 
                        contr:DFromGiver, 
                        varInit: {
                                   fund_address_:address(this),
                                   giver_address_:giver,
                                   lock_time_:lock_time_,
                                   unlock_time_:unlock_time_ } } ) ;  

  TvmCell stateInit = tvm.buildStateInit ( code , dataInit , 0  ) ; 
  can_change_fromgiver_code_ = false ; 
  num_investors_sent_ ++ ;
  address fgaddr = new DFromGiver {
                      value:(FG_MIN_BALANCE + EPSILON_BALANCE),
                      stateInit:stateInit}() ; 

  return fgaddr;
}

function notifyRight (/*uint128 balance ,*/ uint128 income , address giver) external
{ 
  uint256 add_std_address = address(msg.sender).value; // int_sender () ;  
  require (add_std_address == getFromGiverAddress ( giver ) , not_my_giver) ;
  require ( address(this).balance >= EPSILON_BALANCE , balance_too_low);
  require ( now < lock_time_ , time_too_late);
  tvm.accept () ;
  givers_summa_ += income; 
} 

function acknowledgeFinalizeLeft (uint128 quant , uint256 pk , uint128 rate) external 
{
  uint256 add_std_address =  address(msg.sender).value; // int_sender () ;   
  require (add_std_address == getKWDPoolAddress ( pk , quant , rate) , not_my_investor) ;  
//  require ( address(this).balance >= EPSILON_BALANCE , balance_too_low);  
  tvm.accept() ;

  num_investors_received_ ++ ; 
}   

function acknowledgeFinalizeRight (address giver) external 
{ 
  uint256 add_std_address = address(msg.sender).value; // int_sender () ;  
  require (add_std_address == getFromGiverAddress ( giver ) , not_my_giver) ;  
//  require ( address(this).balance >= EPSILON_BALANCE , balance_too_low);  
  tvm.accept() ;

  num_investors_received_ ++ ; 
}



function finalize (address addr) external view
{
   require (msg.pubkey() == tvm.pubkey() ,not_my_pubkey);
   require (now >= lock_time_ && now <= unlock_time_ , time_not_inside);
   require ( address(this).balance >=GAS_FOR_PARTICIPANT_MESSAGE + EPSILON_BALANCE , balance_too_low);
   require (math.min(investors_summa_ , givers_summa_) >= min_summa_ , sum_too_small);
   require ( num_investors_received_ != num_investors_sent_ , not_all_ack ) ;
   tvm.accept();
   IKWFundParticipant(addr).notifyParticipant{value:GAS_FOR_PARTICIPANT_MESSAGE}(investors_summa_ , givers_summa_) ; 
}

function setFundCode (TvmCell code) public view
{
   require (msg.pubkey() == tvm.pubkey() , not_my_pubkey);
   require ( num_investors_received_ == num_investors_sent_ , not_all_ack);
   require (now >= lock_time_ && now <= unlock_time_ , time_not_inside);
   require (address(this).balance >= RESPAWN_BALANCE , balance_too_low);
   tvm.setcode (code); 
   tvm.setCurrentCode (code); 
}

}
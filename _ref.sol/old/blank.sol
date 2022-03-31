

pragma ton-solidity ^0.53.0;

import "IBlank.sol";
import "IKWDPool.sol";
import "IFromGiver.sol";

contract Blank {


uint128 constant MIN_VALUE = 100000;
uint8 constant MINIMUM_GAS_FOR_COMPUTE = 5;
uint8 constant DEFAULT_MSG_FLAGS = 0;

uint256 kwdpool_code_;
uint256 fromgiver_code_;
uint256 deployer_pubkey_ ;
address investor_address_ ;
uint128 balance_ ;
uint128 givers_summa_;
uint128 investors_summa_;
uint128 min_summa_;
uint128 max_summa_;
bool ready_;
uint256 lock_time_ ;
uint256 unlock_time_;

constructor(uint128 min_summa , uint128 max_summa) public {
   givers_summa_ = 0;
   investors_summa_ = 0;
   min_summa_ = min_summa;
   max_summa_ = max_summa;
   ready_ = false; 
}

function setKWDPoolCode(uint256 code) public
{
   require (msg.pubkey() == tvm.pubkey() , 2);
   kwdpool_code_ = code;
}


function setFromGiverCode(uint256 code) public
{
require (msg.pubkey() == tvm.pubkey() , 2);
   fromgiver_code_ = code;
}


function getKWDPoolAddress(uint256 pubkey , uint128 quant) public returns(uint256)
{
   uint256 dataHash = 0 /* tvm.hash (
                  tvm.buildDataInit({contr:DKWPoolLRecord,
                                     pubkey:pubkey,
                                    varInit:({
                                         address:tvm.address
                                           value:quant})})*/ ; 
  uint256 add_std_address = tvm.stateInitHash(kwdpool_code_ , dataHash , 0 , 0);
  return add_std_address ;
}
 

function notifyLeft(uint128 balance , uint128 quant ) public {   
  uint256 add_std_address = (msg.sender).value;
  require (add_std_address ==
             getKWDPoolAddress(msg.pubkey() , quant ) , 2 );
  tvm.accept(); 
  investors_summa_ += balance;  
}
   

function getFromGiverAddress(uint256 pubkey , address fg_address)  private returns(uint256){
  uint256 dataHash = 0 /* tvm_hash (tvm_buildDataInit_ ({
                  contr:FromGiver,
                  pubkey:pubkey,
                  varInit:({
                             address:tvm.address,
                             value:fg_address
                              })})*/ ;
  uint256 add_std_address = tvm.stateInitHash(kwdpool_code_ , dataHash , 0 , 0);
  return add_std_address ; 
} 

function notifyRight(uint128 balance , address fg_address) public 
{ 
  uint256 add_std_address = (msg.sender).value;
  require (add_std_address == getFromGiverAddress(msg.pubkey(), fg_address) , 2);
  tvm.accept();
  givers_summa_ += balance;
}


          
function finalize(address addr) public
{
require ((now >= lock_time_) && (now <= unlock_time_) , 2);
   tvm.accept();
   IBlank (addr).notifyParticipant{flag:MINIMUM_GAS_FOR_COMPUTE} (investors_summa_ , givers_summa_) ;
   ready_ = true; 

// emit

}


function getReady() public view returns (bool)  
{
    return ready_;
}

}



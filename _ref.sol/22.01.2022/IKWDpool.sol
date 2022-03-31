
pragma ton-solidity >=0.54.0;

interface IKWDpool {

constructor(optional (address) x1) external ;
function setFinalAddress (address x1) external ;
receive() external ; 
function notifyParticipant (uint128 x1 , uint128 x2 , uint128 x3) external ;
function returnFunds(address x1) external ;
function sendFunds(address x1) external ;

}

interface IBlank {
function isFundReady (uint256 pk,uint128 quant,uint8 rate) external ;
function notifyLeft (uint256 pk,uint128 quant,uint8 rate,uint128 balance) external ;
function notifyRight  (address giver,uint128 balance,uint128 income) external ;
function acknowledgeFinalizeRight (address giver) external ;
function acknowledgeFinalizeLeft (uint256 pk,uint128 quant,uint8 rate) external ;
function acknowledgeDeploy(address x1) external ;

}


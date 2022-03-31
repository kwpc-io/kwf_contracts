
pragma ton-solidity >=0.54.0;

interface IBlank {

// constructor (uint128 x1 , uint128 x2) external ;
function notifyLeft (uint256 x1 , uint128 x2 , uint8 x3 , uint128 x4) external ;
function notifyRight (address giver , uint128 balance , uint128 income ) external ;
// function acknowledgeFinalizeRight (address x1) external ;
// function acknowledgeFinalizeLeft (uint128 x1 , uint256 x2 , uint8 x3) external ;
// function isFundReady (uint128 quant , uint256 pk , uint8 rate) external ;
function isFundReady (uint256 pk , uint128 quant , uint8 rate) external ;
function acknowledgeFinalizeLeft (uint128 quant , uint256 pk , uint8 rate) external ;
function acknowledgeFinalizeRight (address giver) external ;
function acknowledgeDeploy (address giver) external;
}

interface IKWFundParticipant {

function notifyParticipant(uint128 x1 , uint128 x2) external ;
function initialize() external ;

}

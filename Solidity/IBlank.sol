
pragma ton-solidity >=0.54.0;

interface IBlank {

function notifyLeft ( uint256 pk , uint256 nonce , uint128 balance, uint128 adj_balance) external ;
function notifyRight (address giver , uint256 nonce, uint128 balance , uint128 income ) external ;
function isFundReady (uint256 pk , uint256 nonce ) external ;
function acknowledgeFinalizeLeft ( uint256 pk , uint256 nonce) external ;
function acknowledgeFinalizeRight (address giver, uint256 nonce, bool dead_giver) external ;
function acknowledgeDeploy (address giver, uint256 nonce) external;
function vote (uint256 pk , uint256 nonce, bool choice, uint128 sum, uint8 voting_id, uint256 code_hash) external;
}


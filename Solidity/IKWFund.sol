
pragma ton-solidity >=0.54.0;

interface IKWFund {

function sendFromGiverParams (address giver, uint256 nonce, TvmCell  params ) external ;
function sendKWDPoolParams (uint256 pk, uint256 nonce, TvmCell  params ) external ;

}


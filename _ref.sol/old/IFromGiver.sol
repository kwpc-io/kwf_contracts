
pragma ton-solidity >=0.53.0;


interface IFromGiver {
// constructor (address fund_address) external;
receive () external;
function notifyParticipant(uint128 summa_investors , uint128 summa_givers) external;

}
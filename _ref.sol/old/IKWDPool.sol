
pragma ton-solidity >=0.53.0;

interface IKWDPool {
//constructor (address fund_address , uint128 quant , final_address : optional address) external; 
 receive () external;
function notifyParticipant (uint128 summa_investors, uint128 summa_givers) external;
function setFinalAddress (address final_address) external;
}
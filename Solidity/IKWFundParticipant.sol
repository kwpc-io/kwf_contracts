
pragma ton-solidity >=0.54.0;


interface IKWFundParticipant {

function notifyParticipant (bool giveup, uint128 summa_investors , uint128 summa_givers) external ;
function initialize (uint32 lock_time, 
                     uint32 unlock_time, 
                     uint128 quant,
                     uint8 rate,
                     uint32 kwf_lock_time) external ; 
function sendFunds (TvmCell code) external; 
function acknowledgeFunds () external ;   
function onVoteAccept () external;
function onVoteReject (uint8 voting_id) external;                 

}
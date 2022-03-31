
pragma ton-solidity >=0.53.0;

interface IBlank {
//constructor(uint128 min_summa , uint128 max_summa) external;
function setKWDPoolCode(uint256 code) external;
function setFromGiverCode(uint256 code) external;
function getKWDPoolAddress(uint256 pubkey , uint128 quant) external;
function notifyLeft(uint128 balance , uint128 quant ) external;
function notifyRight(uint128 balance , address fg_address) external;
function finalize(address addr) external;
function getReady() external;
function notifyParticipant (uint128 summa_investors, uint128 summa_givers) external;

}
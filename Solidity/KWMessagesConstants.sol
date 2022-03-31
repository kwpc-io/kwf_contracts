pragma ton-solidity >=0.54.0;

library KWMessages {

uint128 constant BLANK_MIN_BALANCE = 20 ton ;
uint128 constant RESPAWN_BALANCE = 50 ton;
uint128 constant EPSILON_BALANCE = 0.5 ton ;
uint128 constant GAS_FOR_PARTICIPANT_MESSAGE = 0.5 ton ;

uint128 constant KWD_MIN_BALANCE = 5 ton ;
uint128 constant GAS_FOR_FUND_MESSAGE = 0.5 ton ;

uint128 constant FG_MIN_BALANCE = 5 ton ;

uint16 constant ALL_BALANCE_MSG_FLAG = 128 ;
uint16 constant DEFAULT_MSG_FLAGS = 0 ;
uint16 constant MSG_VALUE_BUT_FEE_FLAGS = 64 ;

uint128 constant VOTING_FEE = 0.5 ton;

uint32 constant TIME_FOR_FUNDS_COLLECTING = 3 days;
uint32 constant TIME_FOR_SETCODE_PREPARE  = 4 days;
uint32 constant MIN_VOTING_TIME = 3 minutes;

}
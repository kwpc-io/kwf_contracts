pragma ton-solidity >=0.54.0;

library KWErrors {

uint16 constant error_not_external_message = 101 ;
uint16 constant error_not_my_pubkey = 102 ;
uint16 constant error_balance_too_low = 103 ;
uint16 constant error_time_too_late = 104 ;
uint16 constant error_quant_not_set = 105 ;
uint16 constant error_farm_rate_not_set = 106 ;
uint16 constant error_msg_value_too_low = 107 ;
uint16 constant error_not_my_fund = 108 ;
uint16 constant error_time_not_inside = 109 ;
uint16 constant error_fund_ready_set = 110 ;
uint16 constant error_final_address_not_set = 111 ;
uint16 constant error_balance_not_positive = 112 ;
uint16 constant error_fund_ready_not_set = 113 ;
uint16 constant error_time_too_early = 114 ;
uint16 constant error_not_initialized = 115 ;
uint16 constant error_initialized = 116 ;
uint16 constant error_fund_not_set = 117 ;
uint16 constant error_return_address_is_mine = 118 ;

uint16 constant error_not_internal_message = 119 ;
uint16 constant error_cant_initialize = 120 ;
uint16 constant error_not_my_giver = 121 ;
uint16 constant error_unlock_time_less_lock = 122 ;

uint16 constant error_not_my_code = 123 ;
uint16 constant error_not_my_investor = 124 ;
uint16 constant error_not_all_ack = 125 ;
uint16 constant error_giver_not_set = 126 ;
uint16 constant error_cannot_change_code = 127 ;
uint16 constant error_sum_too_small = 128 ;
uint16 constant error_max_summa_less_min = 129 ;
uint16 constant error_rate_not_set = 130 ;
uint16 constant error_kwf_lock_time_not_set = 131;
uint16 constant error_already_all_ack = 132 ;

uint16 constant error_already_voted = 133;
uint16 constant error_code_not_correct = 134;
uint16 constant voting_fee_too_low = 135;
uint16 constant voting_time_too_low = 136;
uint16 constant voting_time_too_long = 137;

}
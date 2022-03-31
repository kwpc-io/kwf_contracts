Require Import UMLang.UrsusLib.
Require Import CommonTypes. 
Locate InternalMessageParamsFields.

Class KWMessagesCommonConsts:= {
KWMessages_ι_MIN_VOTING_TIME_ :  XUInteger32 ;
KWMessages_ι_TIME_FOR_SETCODE_PREPARE_ :  XUInteger32 ;
KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_ :  XUInteger32 ;
KWMessages_ι_VOTING_FEE_ :  XUInteger128 ;
KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :  XUInteger16 ;
KWMessages_ι_DEFAULT_MSG_FLAGS_ :  XUInteger16 ;
KWMessages_ι_ALL_BALANCE_MSG_FLAG_ :  XUInteger16 ;
KWMessages_ι_FG_MIN_BALANCE_ :  XUInteger128 ;
KWMessages_ι_GAS_FOR_FUND_MESSAGE_ :  XUInteger128 ;
KWMessages_ι_KWD_MIN_BALANCE_ :  XUInteger128 ;
KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_ :  XUInteger128 ;
KWMessages_ι_EPSILON_BALANCE_ :  XUInteger128 ;
KWMessages_ι_RESPAWN_BALANCE_ :  XUInteger128 ;
KWMessages_ι_BLANK_MIN_BALANCE_ :  XUInteger128 ;
} .

Class KWErrorsCommonErrors:= {
KWErrors_ι_error_code_not_correct_ : ErrorType;
KWErrors_ι_error_already_voted_ : ErrorType;
KWErrors_ι_error_already_all_ack_ : ErrorType;
KWErrors_ι_error_kwf_lock_time_not_set_ : ErrorType;
KWErrors_ι_error_rate_not_set_ : ErrorType;
KWErrors_ι_error_max_summa_less_min_ : ErrorType;
KWErrors_ι_error_sum_too_small_ : ErrorType;
KWErrors_ι_error_cannot_change_code_ : ErrorType;
KWErrors_ι_error_giver_not_set_ : ErrorType;
KWErrors_ι_error_not_all_ack_ : ErrorType;
KWErrors_ι_error_not_my_investor_ : ErrorType;
KWErrors_ι_error_not_my_code_ : ErrorType;
KWErrors_ι_error_unlock_time_less_lock_ : ErrorType;
KWErrors_ι_error_not_my_giver_ : ErrorType;
KWErrors_ι_error_cant_initialize_ : ErrorType;
KWErrors_ι_error_not_internal_message_ : ErrorType;
KWErrors_ι_error_return_address_is_mine_ : ErrorType;
KWErrors_ι_error_fund_not_set_ : ErrorType;
KWErrors_ι_error_initialized_ : ErrorType;
KWErrors_ι_error_not_initialized_ : ErrorType;
KWErrors_ι_error_time_too_early_ : ErrorType;
KWErrors_ι_error_fund_ready_not_set_ : ErrorType;
KWErrors_ι_error_balance_not_positive_ : ErrorType;
KWErrors_ι_error_final_address_not_set_ : ErrorType;
KWErrors_ι_error_fund_ready_set_ : ErrorType;
KWErrors_ι_error_time_not_inside_ : ErrorType;
KWErrors_ι_error_not_my_fund_ : ErrorType;
KWErrors_ι_error_msg_value_too_low_ : ErrorType;
KWErrors_ι_error_farm_rate_not_set_ : ErrorType;
KWErrors_ι_error_quant_not_set_ : ErrorType;
KWErrors_ι_error_time_too_late_ : ErrorType;
KWErrors_ι_error_balance_too_low_ : ErrorType;
KWErrors_ι_error_not_my_pubkey_ : ErrorType;
KWErrors_ι_error_not_external_message_ : ErrorType;
} .
Class KWErrorsCommonConsts:= {
KWErrors_ι_voting_time_too_long_ :  XUInteger16 ;
KWErrors_ι_voting_time_too_low_ :  XUInteger16 ;
KWErrors_ι_voting_fee_too_low_ :  XUInteger16 ;
} .
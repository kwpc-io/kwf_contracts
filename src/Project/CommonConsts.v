
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmCells.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

Local Open Scope N_scope.

#[global] 
Instance  KWMessages_Consts :KWMessagesCommonConsts:= {
KWMessages_ι_MIN_VOTING_TIME_:= Build_XUBInteger 180;
KWMessages_ι_TIME_FOR_SETCODE_PREPARE_:= Build_XUBInteger 345600;
KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_:= Build_XUBInteger 259200;
KWMessages_ι_VOTING_FEE_:= Build_XUBInteger 500000000;
KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_:= Build_XUBInteger 64;
KWMessages_ι_DEFAULT_MSG_FLAGS_:= Build_XUBInteger 0;
KWMessages_ι_ALL_BALANCE_MSG_FLAG_:= Build_XUBInteger 128;
KWMessages_ι_FG_MIN_BALANCE_:= Build_XUBInteger 5000000000;
KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= Build_XUBInteger 500000000;
KWMessages_ι_KWD_MIN_BALANCE_:= Build_XUBInteger 5000000000;
KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:= Build_XUBInteger 500000000;
KWMessages_ι_EPSILON_BALANCE_:= Build_XUBInteger 500000000;
KWMessages_ι_RESPAWN_BALANCE_:= Build_XUBInteger 50000000000;
KWMessages_ι_BLANK_MIN_BALANCE_:= Build_XUBInteger 20000000000;
} .

#[global] 
Instance  KWErrors_Errors :KWErrorsCommonErrors:= {
KWErrors_ι_error_code_not_correct_:= 134;
KWErrors_ι_error_already_voted_:= 133;
KWErrors_ι_error_already_all_ack_:= 132;
KWErrors_ι_error_kwf_lock_time_not_set_:= 131;
KWErrors_ι_error_rate_not_set_:= 130;
KWErrors_ι_error_max_summa_less_min_:= 129;
KWErrors_ι_error_sum_too_small_:= 128;
KWErrors_ι_error_cannot_change_code_:= 127;
KWErrors_ι_error_giver_not_set_:= 126;
KWErrors_ι_error_not_all_ack_:= 125;
KWErrors_ι_error_not_my_investor_:= 124;
KWErrors_ι_error_not_my_code_:= 123;
KWErrors_ι_error_unlock_time_less_lock_:= 122;
KWErrors_ι_error_not_my_giver_:= 121;
KWErrors_ι_error_cant_initialize_:= 120;
KWErrors_ι_error_not_internal_message_:= 119;
KWErrors_ι_error_return_address_is_mine_:= 118;
KWErrors_ι_error_fund_not_set_:= 117;
KWErrors_ι_error_initialized_:= 116;
KWErrors_ι_error_not_initialized_:= 115;
KWErrors_ι_error_time_too_early_:= 114;
KWErrors_ι_error_fund_ready_not_set_:= 113;
KWErrors_ι_error_balance_not_positive_:= 112;
KWErrors_ι_error_final_address_not_set_:= 111;
KWErrors_ι_error_fund_ready_set_:= 110;
KWErrors_ι_error_time_not_inside_:= 109;
KWErrors_ι_error_not_my_fund_:= 108;
KWErrors_ι_error_msg_value_too_low_:= 107;
KWErrors_ι_error_farm_rate_not_set_:= 106;
KWErrors_ι_error_quant_not_set_:= 105;
KWErrors_ι_error_time_too_late_:= 104;
KWErrors_ι_error_balance_too_low_:= 103;
KWErrors_ι_error_not_my_pubkey_:= 102;
KWErrors_ι_error_not_external_message_:= 101;
} .
#[global] 
Instance  KWErrors_Consts :KWErrorsCommonConsts:= {
KWErrors_ι_voting_time_too_long_:= Build_XUBInteger 137;
KWErrors_ι_voting_time_too_low_:= Build_XUBInteger 136;
KWErrors_ι_voting_fee_too_low_:= Build_XUBInteger 135;
} .
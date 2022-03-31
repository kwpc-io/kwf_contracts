Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import Psatz. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.
Require Import UrsusStdLib.Cpp.stdErrors. 
Require Import UrsusStdLib.Cpp.stdFunc.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdUFunc.
Require Import UrsusStdLib.Cpp.stdFuncNotations.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

Require Import PseudoFund.DPseudoFund.Ledger.
Require Import PseudoFund.DPseudoFund.ClassTypesNotations.
Require Import PseudoFund.DPseudoFund.ClassTypes.
Require Import PseudoFund.DPseudoFund.Functions.FuncSig.
Require Import PseudoFund.DPseudoFund.Functions.FuncNotations.


Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypesNotations.

Require Import Contracts.FromGiver.DFromGiver.Interface.
Require Import Contracts.FromGiver.DFromGiver.ClassTypes.
Require Import Contracts.FromGiver.DFromGiver.ClassTypesNotations.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypesNotations.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypesNotations.

Require Import Contracts.KWDPool.DKWDPool.Interface.
Require Import Contracts.KWDPool.DKWDPool.ClassTypes.
Require Import Contracts.KWDPool.DKWDPool.ClassTypesNotations.

(* Require Import Contracts.KWErrorConstants.KWErrors.Interface.
Require Import Contracts.KWErrorConstants.KWErrors.ClassTypes.
Require Import Contracts.KWErrorConstants.KWErrors.ClassTypesNotations.

Require Import Contracts.KWMessagesConstants.KWMessages.Interface.
Require Import Contracts.KWMessagesConstants.KWMessages.ClassTypes.
Require Import Contracts.KWMessagesConstants.KWMessages.ClassTypesNotations. *)

Set Typeclasses Iterative Deepening.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

#[local]
Existing Instance LedgerPruvendoRecord.

Section  DPseudoFundFuncs.

Context `{KWErrorsCommonErrors}.
(*Context `{KWErrorsCommonConsts}*) 
(*Context `{KWMessagesCommonConsts}*)

Context {KWErrors_ι_voting_time_too_long_  :  XUInteger16  }. 
Notation " 'KWErrors.voting_time_too_long' " := (sInject KWErrors_ι_voting_time_too_long_) (in custom URValue at level 0) : ursus_scope. 
Context {KWErrors_ι_voting_time_too_low_  :  XUInteger16  }. 
Notation " 'KWErrors.voting_time_too_low' " := (sInject KWErrors_ι_voting_time_too_low_) (in custom URValue at level 0) : ursus_scope. 
Context {KWErrors_ι_voting_fee_too_low_  :  XUInteger16  }. 
Notation " 'KWErrors.voting_fee_too_low' " := (sInject KWErrors_ι_voting_fee_too_low_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_code_not_correct' " := (sInject KWErrors_ι_error_code_not_correct_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_already_voted' " := (sInject KWErrors_ι_error_already_voted_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_already_all_ack' " := (sInject KWErrors_ι_error_already_all_ack_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_kwf_lock_time_not_set' " := (sInject KWErrors_ι_error_kwf_lock_time_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_rate_not_set' " := (sInject KWErrors_ι_error_rate_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_max_summa_less_min' " := (sInject KWErrors_ι_error_max_summa_less_min_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_sum_too_small' " := (sInject KWErrors_ι_error_sum_too_small_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_cannot_change_code' " := (sInject KWErrors_ι_error_cannot_change_code_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_giver_not_set' " := (sInject KWErrors_ι_error_giver_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_all_ack' " := (sInject KWErrors_ι_error_not_all_ack_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_my_investor' " := (sInject KWErrors_ι_error_not_my_investor_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_my_code' " := (sInject KWErrors_ι_error_not_my_code_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_unlock_time_less_lock' " := (sInject KWErrors_ι_error_unlock_time_less_lock_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_my_giver' " := (sInject KWErrors_ι_error_not_my_giver_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_cant_initialize' " := (sInject KWErrors_ι_error_cant_initialize_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_internal_message' " := (sInject KWErrors_ι_error_not_internal_message_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_return_address_is_mine' " := (sInject KWErrors_ι_error_return_address_is_mine_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_fund_not_set' " := (sInject KWErrors_ι_error_fund_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_initialized' " := (sInject KWErrors_ι_error_initialized_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_initialized' " := (sInject KWErrors_ι_error_not_initialized_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_time_too_early' " := (sInject KWErrors_ι_error_time_too_early_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_fund_ready_not_set' " := (sInject KWErrors_ι_error_fund_ready_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_balance_not_positive' " := (sInject KWErrors_ι_error_balance_not_positive_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_final_address_not_set' " := (sInject KWErrors_ι_error_final_address_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_fund_ready_set' " := (sInject KWErrors_ι_error_fund_ready_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_time_not_inside' " := (sInject KWErrors_ι_error_time_not_inside_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_my_fund' " := (sInject KWErrors_ι_error_not_my_fund_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_msg_value_too_low' " := (sInject KWErrors_ι_error_msg_value_too_low_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_farm_rate_not_set' " := (sInject KWErrors_ι_error_farm_rate_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_quant_not_set' " := (sInject KWErrors_ι_error_quant_not_set_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_time_too_late' " := (sInject KWErrors_ι_error_time_too_late_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_balance_too_low' " := (sInject KWErrors_ι_error_balance_too_low_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_my_pubkey' " := (sInject KWErrors_ι_error_not_my_pubkey_) (in custom URValue at level 0) : ursus_scope. 
Notation " 'KWErrors.error_not_external_message' " := (sInject KWErrors_ι_error_not_external_message_) (in custom URValue at level 0) : ursus_scope. 

Context {KWMessages_ι_MIN_VOTING_TIME_  :  XUInteger32  }. 
Notation " 'KWMessages.MIN_VOTING_TIME' " := (sInject KWMessages_ι_MIN_VOTING_TIME_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_TIME_FOR_SETCODE_PREPARE_  :  XUInteger32  }. 
Notation " 'KWMessages.TIME_FOR_SETCODE_PREPARE' " := (sInject KWMessages_ι_TIME_FOR_SETCODE_PREPARE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_  :  XUInteger32  }. 
Notation " 'KWMessages.TIME_FOR_FUNDS_COLLECTING' " := (sInject KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_VOTING_FEE_  :  XUInteger128  }. 
Notation " 'KWMessages.VOTING_FEE' " := (sInject KWMessages_ι_VOTING_FEE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_  :  XUInteger16  }. 
Notation " 'KWMessages.MSG_VALUE_BUT_FEE_FLAGS' " := (sInject KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_DEFAULT_MSG_FLAGS_  :  XUInteger16  }. 
Notation " 'KWMessages.DEFAULT_MSG_FLAGS' " := (sInject KWMessages_ι_DEFAULT_MSG_FLAGS_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_ALL_BALANCE_MSG_FLAG_  :  XUInteger16  }. 
Notation " 'KWMessages.ALL_BALANCE_MSG_FLAG' " := (sInject KWMessages_ι_ALL_BALANCE_MSG_FLAG_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_FG_MIN_BALANCE_  :  XUInteger128  }. 
Notation " 'KWMessages.FG_MIN_BALANCE' " := (sInject KWMessages_ι_FG_MIN_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_GAS_FOR_FUND_MESSAGE_  :  XUInteger128  }. 
Notation " 'KWMessages.GAS_FOR_FUND_MESSAGE' " := (sInject KWMessages_ι_GAS_FOR_FUND_MESSAGE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_KWD_MIN_BALANCE_  :  XUInteger128  }. 
Notation " 'KWMessages.KWD_MIN_BALANCE' " := (sInject KWMessages_ι_KWD_MIN_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_  :  XUInteger128  }. 
Notation " 'KWMessages.GAS_FOR_PARTICIPANT_MESSAGE' " := (sInject KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_EPSILON_BALANCE_  :  XUInteger128  }. 
Notation " 'KWMessages.EPSILON_BALANCE' " := (sInject KWMessages_ι_EPSILON_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_RESPAWN_BALANCE_  :  XUInteger128  }. 
Notation " 'KWMessages.RESPAWN_BALANCE' " := (sInject KWMessages_ι_RESPAWN_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
Context {KWMessages_ι_BLANK_MIN_BALANCE_  :  XUInteger128  }. 
Notation " 'KWMessages.BLANK_MIN_BALANCE' " := (sInject KWMessages_ι_BLANK_MIN_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
#[local]
Definition public  := UExpression .
#[local]
Definition private := UExpression .
#[local]
Definition external := UExpression .
#[local]
Definition internal := UExpression .
#[local]
Definition modifier := forall X b, UExpression X b -> UExpression X true .
Tactic Notation "unfold_mod" := (unfold modifier; intros X b u).


Definition getKWDPoolAddress_ (pubkey :  XUInteger256 ) (nonce :  XUInteger256 ): internal ( XUInteger256 ) false .
  refine {{  new 'dataCell : (  cell_   ) @ "dataCell"  := tvm_buildDataInit(
      [$ #{"DKWDPool"} ⇒ {DataInitInit_ι_contr};
#{pubkey} ⇒ {DataInitInit_ι_pubkey};
      [$ 
        tvm_myaddr() ⇒ {KWDPool.DKWDPool.ClassTypes.VarInit_ι_fund_address_};
        #{nonce} ⇒ {KWDPool.DKWDPool.ClassTypes.VarInit_ι_nonce_}
      $] ⇒ {DataInitInit_ι_varInit}
$]) ; { _ } }}. 
  refine {{  new 'dataHash : (  XUInteger256  ) @ "dataHash"  := tvm_hash(!{dataCell}) ; { _ } }}. 
  refine {{  new 'dataDepth : (  XUInteger16  ) @ "dataDepth"  := !{dataCell} -> cell.depth ( ) ; { _ } }}. 
  refine {{  new 'add_std_address : (  XUInteger256  ) @ "add_std_address"  := tvm_stateInitHash(kwdpool_code_hash_, !{dataHash}, kwdpool_code_depth_, !{dataDepth}) ; { _ } }}. 
  refine {{ return_ !{add_std_address} }}.
Defined. 
Definition getKWDPoolAddress_right {b0 b1}
(pubkey: URValue  XUInteger256  b0 ) 
(nonce: URValue  XUInteger256  b1 ) : URValue ( XUInteger256 ) (orb b1 b0) :=
wrapURExpression (ursus_call_with_args λ2 getKWDPoolAddress_ pubkey nonce).
Notation " 'getKWDPoolAddress' '(' pubkey ',' nonce ')' " := 
(getKWDPoolAddress_right pubkey nonce)  
(in custom URValue at level 0 , 
pubkey custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition check_investor (pk :  XUInteger256 ) (nonce :  XUInteger256 ): modifier .
unfold_mod.
  refine {{  new 'add_std_address : (  XUInteger256  ) @ "add_std_address"  := int_sender() ↑ address.address ; { _ } }}. 
  refine {{ require_((!{add_std_address} == getKWDPoolAddress(#{pk}, #{nonce})), KWErrors.error_not_my_investor) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_investor _ _ {_} {_}.

Definition sendKWDPoolParams_ (pk :  XUInteger256 ) (nonce :  XUInteger256 ) (NO_NAME2 :  cell_  ): external PhantomType true .
  refine (check_investor pk nonce _) .
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        KWMessages.GAS_FOR_PARTICIPANT_MESSAGE ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.acknowledgeFunds( ) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition sendKWDPoolParams_left {R b0 b1 b2 } 
(pk: URValue  XUInteger256  b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
(NO_NAME2: URValue  cell_   b2 ) 
 : UExpression R (orb(orb(orb true b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ3 sendKWDPoolParams_ pk nonce NO_NAME2 ).
Notation " 'sendKWDPoolParams' '(' pk ',' nonce ',' NO_NAME2 ')' " := 
(sendKWDPoolParams_left pk nonce NO_NAME2 )  
(in custom ULValue at level 0 , 
pk custom URValue at level 0, 
nonce custom URValue at level 0, 
NO_NAME2 custom URValue at level 0) : ursus_scope.

Definition buildFromGiverDataInitCell_ (giver :  address  ) (nonce :  XUInteger256 ): internal ( cell_  ) false .
  refine {{  new 'dataCell : (  cell_   ) @ "dataCell"  := tvm_buildDataInit(
      [$ #{"DFromGiver"} ⇒ {DataInitInit_ι_contr};
      [$ 
        tvm_myaddr() ⇒ {FromGiver.DFromGiver.ClassTypes.VarInit_ι_fund_address_};
        #{giver} ⇒ {FromGiver.DFromGiver.ClassTypes.VarInit_ι_giver_address_};
        #{nonce} ⇒ {FromGiver.DFromGiver.ClassTypes.VarInit_ι_nonce_}
      $] ⇒ {DataInitInit_ι_varInit}
$]) ; { _ } }}. 
  refine {{ return_ !{dataCell} }}.
Defined. 
Definition buildFromGiverDataInitCell_right {b0 b1}
(giver: URValue  address   b0 ) 
(nonce: URValue  XUInteger256  b1 ) : URValue ( cell_  ) (orb b1 b0) :=
wrapURExpression (ursus_call_with_args λ2 buildFromGiverDataInitCell_ giver nonce).
Notation " 'buildFromGiverDataInitCell' '(' giver ',' nonce ')' " := 
(buildFromGiverDataInitCell_right giver nonce)  
(in custom URValue at level 0 , 
giver custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition getFromGiverAddress_ (giver :  address  ) (nonce :  XUInteger256 ): internal ( XUInteger256 ) false .
  refine {{  new 'dataCell : (  cell_   ) @ "dataCell"  := buildFromGiverDataInitCell(#{giver}, #{nonce}) ; { _ } }}. 
  refine {{  new 'dataHash : (  XUInteger256  ) @ "dataHash"  := tvm_hash(!{dataCell}) ; { _ } }}. 
  refine {{  new 'dataDepth : (  XUInteger16  ) @ "dataDepth"  := !{dataCell} -> cell.depth ( ) ; { _ } }}. 
  refine {{  new 'add_std_address : (  XUInteger256  ) @ "add_std_address"  := tvm_stateInitHash(fromgiver_code_hash_, !{dataHash}, fromgiver_code_depth_, !{dataDepth}) ; { _ } }}. 
  refine {{ return_ !{add_std_address} }}.
Defined. 
Definition getFromGiverAddress_right {b0 b1}
(giver: URValue  address   b0 ) 
(nonce: URValue  XUInteger256  b1 ) : URValue ( XUInteger256 ) (orb b1 b0) :=
wrapURExpression (ursus_call_with_args λ2 getFromGiverAddress_ giver nonce).
Notation " 'getFromGiverAddress' '(' giver ',' nonce ')' " := 
(getFromGiverAddress_right giver nonce)  
(in custom URValue at level 0 , 
giver custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition check_giver (giver :  address  ) (nonce :  XUInteger256 ): modifier .
unfold_mod.
  refine {{  new 'add_std_address : (  XUInteger256  ) @ "add_std_address"  := int_sender() ↑ address.address ; { _ } }}. 
  refine {{ require_((!{add_std_address} == getFromGiverAddress(#{giver}, #{nonce})), KWErrors.error_not_my_giver) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_giver _ _ {_} {_}.

Definition sendFromGiverParams_ (giver :  address  ) (nonce :  XUInteger256 ) (NO_NAME2 :  cell_  ): external PhantomType true .
  refine (check_giver giver nonce _) .
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        KWMessages.GAS_FOR_PARTICIPANT_MESSAGE ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.acknowledgeFunds( ) ; { _ } }}. 
  (* TODO *)
  (* refine {{ num_from_givers_ -- ; { _ } }}.  *)
  refine {{ return_ {} }}.
Defined. 
Definition sendFromGiverParams_left {R b0 b1 b2 } 
(giver: URValue  address   b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
(NO_NAME2: URValue  cell_   b2 ) 
 : UExpression R (orb(orb(orb true b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ3 sendFromGiverParams_ giver nonce NO_NAME2 ).
Notation " 'sendFromGiverParams' '(' giver ',' nonce ',' NO_NAME2 ')' " := 
(sendFromGiverParams_left giver nonce NO_NAME2 )  
(in custom ULValue at level 0 , 
giver custom URValue at level 0, 
nonce custom URValue at level 0, 
NO_NAME2 custom URValue at level 0) : ursus_scope.

Definition check_owner : modifier .
unfold_mod.
  refine {{ require_((msg_pubkey() != (β #{0})), KWErrors.error_not_external_message) ; { _ } }}. 
  refine {{ require_((tvm_pubkey() == msg_pubkey()), KWErrors.error_not_my_pubkey) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_owner  {_} {_}.

Definition killFund_ (address_to :  address  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((#{address_to} != tvm_myaddr()), KWErrors.error_return_address_is_mine) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ suicide_(#{address_to}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition killFund_left {R b0 } 
(address_to: URValue  address   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 killFund_ address_to ).
Notation " 'killFund' '(' address_to ')' " := 
(killFund_left address_to )  
(in custom ULValue at level 0 , 
address_to custom URValue at level 0) : ursus_scope.

Definition transferFundsTo_ (kwdp_address :  address  ) (code :  cell_  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((tvm_balance() >= (KWMessages.GAS_FOR_PARTICIPANT_MESSAGE + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  (* TODO *)
  (* refine {{ require_((num_from_givers_ == (β #{0}))) ; { _ } }}.  *)
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ #{kwdp_address} ]] with 
      [$ 
        KWMessages.GAS_FOR_PARTICIPANT_MESSAGE ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.sendFunds(#{code}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition transferFundsTo_left {R b0 b1 } 
(kwdp_address: URValue  address   b0 ) 
(code: URValue  cell_   b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 transferFundsTo_ kwdp_address code ).
Notation " 'transferFundsTo' '(' kwdp_address ',' code ')' " := 
(transferFundsTo_left kwdp_address code )  
(in custom ULValue at level 0 , 
kwdp_address custom URValue at level 0, 
code custom URValue at level 0) : ursus_scope.

Definition getFromGiverFunds_ (from_giver_address :  address  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((tvm_balance() >= (KWMessages.GAS_FOR_PARTICIPANT_MESSAGE + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  (* TODO *)
  (* refine {{ require_((num_from_givers_ > (β #{0}))) ; { _ } }}.  *)
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  new 'empty : (  cell_   ) @ "empty" := {} ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ #{from_giver_address} ]] with 
      [$ 
        KWMessages.GAS_FOR_PARTICIPANT_MESSAGE ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.sendFunds(!{empty}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition getFromGiverFunds_left {R b0 } 
(from_giver_address: URValue  address   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 getFromGiverFunds_ from_giver_address ).
Notation " 'getFromGiverFunds' '(' from_giver_address ')' " := 
(getFromGiverFunds_left from_giver_address )  
(in custom ULValue at level 0 , 
from_giver_address custom URValue at level 0) : ursus_scope.

Definition onCodeUpgrade_ (data_cell :  cell_  ): private PhantomType false .
  refine {{ tvm_resetStorage( ) ; { _ } }}. 
  (* TODO еще с прошлой версии *)
  (* refine {{  new 's : ( slice_  ) @ "s"  := #{data_cell}.toSlice() ; { _ } }}. 
  refine {{ [ [ [ kwdpool_code_hash_, kwdpool_code_depth_ ], fromgiver_code_hash_ ], fromgiver_code_depth_ ] := !{s}.decode( XUInteger256 ,  XUInteger16 ,  XUInteger256 ,  XUInteger16 ) ; { _ } }}. 
  refine {{  new 's1 : ( slice_  ) @ "s1"  := !{s}.loadRefAsSlice() ; { _ } }}. 
  refine {{ [ [ [ [ [ [ givers_summa_, investors_adj_summa_ ], investors_summa_ ], min_summa_ ], max_summa_ ], num_investors_sent_ ], num_from_givers_ ] := !{s1}.decode( XUInteger128 ,  XUInteger128 ,  XUInteger128 ,  XUInteger128 ,  XUInteger128 ,  XUInteger32 ,  XUInteger32 ) ; { _ } }}. 
  refine {{  new 's2 : ( slice_  ) @ "s2"  := !{s}.loadRefAsSlice() ; { _ } }}. 
  refine {{ [ [ [ [ [ lock_time_, unlock_time_ ], farm_rate_ ], kwf_lock_time_ ], quant_ ], nonce_ ] := !{s2}.decode( XUInteger32 ,  XUInteger32 ,  XUInteger8 ,  XUInteger32 ,  XUInteger128 ,  XUInteger256 ) ; { _ } }}.  *)
  refine {{ code_updated := TRUE ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition onCodeUpgrade_left {R b0 } 
(data_cell: URValue  cell_   b0 ) 
 : UExpression R (orb false b0) :=
wrapULExpression (ursus_call_with_args λ1 onCodeUpgrade_ data_cell ).
Notation " 'onCodeUpgrade' '(' data_cell ')' " := 
(onCodeUpgrade_left data_cell )  
(in custom ULValue at level 0 , 
data_cell custom URValue at level 0) : ursus_scope.

Definition constructor_ : public PhantomType (*true*) false .
(* TODO еще с прошлой версии *)
  (* refine {{ revert() ; { _ } }}.  *)
  refine {{ return_ {} }}.
Defined. 
Definition constructor_left {R  } 
 : UExpression R  false  :=
wrapULExpression (ursus_call_with_args λ0 constructor_  ).
Notation " 'constructor' '('  ')' " := 
(constructor_left  )  
(in custom ULValue at level 0 ) : ursus_scope.
End DPseudoFundFuncs .

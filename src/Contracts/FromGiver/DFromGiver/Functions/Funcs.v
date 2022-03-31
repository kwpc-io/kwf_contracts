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

Require Import FromGiver.DFromGiver.Ledger.
Require Import FromGiver.DFromGiver.ClassTypesNotations.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import FromGiver.DFromGiver.Functions.FuncSig.
Require Import FromGiver.DFromGiver.Functions.FuncNotations.


Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypesNotations.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypesNotations.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypesNotations.

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

Section  DFromGiverFuncs.

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




Definition onVoteAccept_ : external PhantomType false .
  refine {{ return_ {} }}.
Defined. 
Definition onVoteAccept_left {R  } 
 : UExpression R  false  :=
wrapULExpression (ursus_call_with_args λ0 onVoteAccept_  ).
Notation " 'onVoteAccept' '('  ')' " := 
(onVoteAccept_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition onVoteReject_ (voting_id :  XUInteger8 ): external PhantomType false .
  refine {{ return_ {} }}.
Defined. 
Definition onVoteReject_left {R b0 } 
(voting_id: URValue  XUInteger8  b0 ) 
 : UExpression R (orb false b0) :=
wrapULExpression (ursus_call_with_args λ1 onVoteReject_ voting_id ).
Notation " 'onVoteReject' '(' voting_id ')' " := 
(onVoteReject_left voting_id )  
(in custom ULValue at level 0 , 
voting_id custom URValue at level 0) : ursus_scope.

Definition _sendFunds_ (address_to :  address  ): internal PhantomType false .
  refine {{  if ( (balance_ > (β #{0})) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ tvm_transfer(#{address_to}, balance_, TRUE, (β #{1}))  }}. 

  refine {{ suicide_(fund_address_) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition _sendFunds_left {R b0 } 
(address_to: URValue  address   b0 ) 
 : UExpression R (orb false b0) :=
wrapULExpression (ursus_call_with_args λ1 _sendFunds_ address_to ).
Notation " '_sendFunds' '(' address_to ')' " := 
(_sendFunds_left address_to )  
(in custom ULValue at level 0 , 
address_to custom URValue at level 0) : ursus_scope.

Definition returnFunds_ : external PhantomType true .
  refine {{ require_((tvm_now() > unlock_time_), KWErrors.error_time_too_early) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ _sendFunds(giver_address_) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition returnFunds_left {R  } 
 : UExpression R  true  :=
wrapULExpression (ursus_call_with_args λ0 returnFunds_  ).
Notation " 'returnFunds' '('  ')' " := 
(returnFunds_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition packParams_ : internal ( cell_  ) false .
  refine {{  new 'main_builder : ( builder_  ) @ "main_builder" := builder() ; { _ } }}. 
  (* TODO *)
  refine {{ {main_builder} := !{main_builder} -> store ( σ fund_address_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> store ( σ lock_time_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> store ( σ unlock_time_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> store ( σ giver_address_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> store ( σ nonce_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> store ( σ balance_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> store ( σ fund_ready_flag_) ; { _ } }}.  
  refine {{ return_ !{main_builder} -> make_cell() }}.
Defined. 
Definition packParams_right : URValue ( cell_  )  false :=
wrapURExpression (ursus_call_with_args λ0 packParams_ ).
Notation " 'packParams' '('  ')' " := 
(packParams_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition check_fund : modifier .
unfold_mod.
  refine {{ require_((int_sender() == fund_address_), KWErrors.error_not_my_fund) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_fund  {_} {_}.

Definition sendFunds_ (NO_NAME0 :  cell_  ): external PhantomType true .
  refine (check_fund  _) .
  refine {{ require_(fund_ready_flag_, KWErrors.error_fund_ready_not_set) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= ((int_value() + balance_) + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IKWFundPtr[[ fund_address_ ]] with 
      [$ 
        (balance_ + int_value()) ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFund.sendFromGiverParams(giver_address_, nonce_, packParams( )) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition sendFunds_left {R b0 } 
(NO_NAME0: URValue  cell_   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 sendFunds_ NO_NAME0 ).
Notation " 'sendFunds' '(' NO_NAME0 ')' " := 
(sendFunds_left NO_NAME0 )  
(in custom ULValue at level 0 , 
NO_NAME0 custom URValue at level 0) : ursus_scope.

Definition acknowledgeFunds_ : external PhantomType true .
  refine (check_fund  _) .
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ tvm_transfer(int_sender(), int_value(), FALSE, (β #{1})) ; { _ } }}. 
  refine {{ suicide_(fund_address_) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition acknowledgeFunds_left {R  } 
 : UExpression R  true  :=
wrapULExpression (ursus_call_with_args λ0 acknowledgeFunds_  ).
Notation " 'acknowledgeFunds' '('  ')' " := 
(acknowledgeFunds_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition notifyParticipant_ (giveup :  XBool  ) (investors_adj_summa_ :  XUInteger128 ) (summa_givers :  XUInteger128 ): external PhantomType true .
  refine (check_fund  _) .
  refine {{ require_(((tvm_now() >= lock_time_) && (tvm_now() <= unlock_time_)), KWErrors.error_time_not_inside) ; { _ } }}. 
  refine {{ require_((~ ( fund_ready_flag_)), KWErrors.error_fund_ready_set) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= ((int_value() + balance_) + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  new 'dead_giver : (  XBool   ) @ "dead_giver"  := (#{giveup} \\ (balance_ == (β #{0}))) ; { _ } }}. 
  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        int_value() ⇒ { Messsage_ι_value};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.acknowledgeFinalizeRight(giver_address_, nonce_, !{dead_giver}) ; { _ } }}. 
  refine {{ if ( !{dead_giver} ) then { {_:UExpression _ false} } else { {_} } ; { _ } }}.
  refine {{ _sendFunds(giver_address_)  }}. 

  refine {{ fund_ready_flag_ := TRUE ; { _ } }}. 
  refine {{  if ( (#{summa_givers} > #{investors_adj_summa_}) ) then { {_:UExpression _ false} }  }}.
  refine {{  new 'extra : (  XUInteger128  ) @ "extra"  := math.muldiv(balance_, (#{summa_givers} - #{investors_adj_summa_}), #{summa_givers}) ; { _ } }}. 
  refine {{ balance_ -= !{extra} ; { _ } }}. 
  refine {{ tvm_transfer(giver_address_, !{extra}, TRUE, (β #{1}))  }}. 


  refine {{ return_ {} }}.
Defined. 
Definition notifyParticipant_left {R b0 b1 b2 } 
(giveup: URValue  XBool   b0 ) 
(investors_adj_summa_: URValue  XUInteger128  b1 ) 
(summa_givers: URValue  XUInteger128  b2 ) 
 : UExpression R (orb(orb(orb true b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ3 notifyParticipant_ giveup investors_adj_summa_ summa_givers ).
Notation " 'notifyParticipant' '(' giveup ',' investors_adj_summa_ ',' summa_givers ')' " := 
(notifyParticipant_left giveup investors_adj_summa_ summa_givers )  
(in custom ULValue at level 0 , 
giveup custom URValue at level 0, 
investors_adj_summa_ custom URValue at level 0, 
summa_givers custom URValue at level 0) : ursus_scope.

Definition receive_ : external PhantomType true .
  refine {{  if ( (int_value() > KWMessages.FG_MIN_BALANCE) ) then { {_:UExpression _ true} } ; { _ } }}.
  refine {{ require_((int_sender() == giver_address_), KWErrors.error_not_my_giver) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ require_((tvm_balance() > (((int_value() + balance_) + KWMessages.GAS_FOR_FUND_MESSAGE) + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        KWMessages.GAS_FOR_FUND_MESSAGE ⇒ { Messsage_ι_value};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.notifyRight(giver_address_, nonce_, balance_, int_value()) ; { _ } }}. 
  refine {{ balance_ += int_value()  }}. 

  refine {{ return_ {} }}.
Defined. 
Definition receive_left {R  } 
 : UExpression R  true  :=
wrapULExpression (ursus_call_with_args λ0 receive_  ).
Notation " 'receive' '('  ')' " := 
(receive_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition initialize_ (NO_NAME0 :  XUInteger32 ) (NO_NAME1 :  XUInteger32 ) (NO_NAME2 :  XUInteger128 ) (NO_NAME3 :  XUInteger8 ) (NO_NAME4 :  XUInteger32 ): external PhantomType true .
  refine {{ revert_(KWErrors.error_cant_initialize) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition initialize_left {R b0 b1 b2 b3 b4 } 
(NO_NAME0: URValue  XUInteger32  b0 ) 
(NO_NAME1: URValue  XUInteger32  b1 ) 
(NO_NAME2: URValue  XUInteger128  b2 ) 
(NO_NAME3: URValue  XUInteger8  b3 ) 
(NO_NAME4: URValue  XUInteger32  b4 ) 
 : UExpression R (orb(orb(orb(orb(orb true b4)b3)b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ5 initialize_ NO_NAME0 NO_NAME1 NO_NAME2 NO_NAME3 NO_NAME4 ).
Notation " 'initialize' '(' NO_NAME0 ',' NO_NAME1 ',' NO_NAME2 ',' NO_NAME3 ',' NO_NAME4 ')' " := 
(initialize_left NO_NAME0 NO_NAME1 NO_NAME2 NO_NAME3 NO_NAME4 )  
(in custom ULValue at level 0 , 
NO_NAME0 custom URValue at level 0, 
NO_NAME1 custom URValue at level 0, 
NO_NAME2 custom URValue at level 0, 
NO_NAME3 custom URValue at level 0, 
NO_NAME4 custom URValue at level 0) : ursus_scope.

Definition constructor_ (lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ): public PhantomType true .
  refine (check_fund  _) .
  refine {{ require_((~ ( fund_address_== {})), KWErrors.error_not_internal_message) ; { _ } }}. 
  refine {{ require_((tvm_now() < #{lock_time}), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ require_((#{lock_time} < #{unlock_time}), KWErrors.error_unlock_time_less_lock) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ balance_ := (β #{0}) ; { _ } }}. 
  refine {{ fund_ready_flag_ := FALSE ; { _ } }}. 
  refine {{ lock_time_ := #{lock_time} ; { _ } }}. 
  refine {{ unlock_time_ := #{unlock_time} ; { _ } }}. 
  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        KWMessages.GAS_FOR_FUND_MESSAGE ⇒ { Messsage_ι_value};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.acknowledgeDeploy(giver_address_, nonce_) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition constructor_left {R b0 b1 } 
(lock_time: URValue  XUInteger32  b0 ) 
(unlock_time: URValue  XUInteger32  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 constructor_ lock_time unlock_time ).
Notation " 'constructor' '(' lock_time ',' unlock_time ')' " := 
(constructor_left lock_time unlock_time )  
(in custom ULValue at level 0 , 
lock_time custom URValue at level 0, 
unlock_time custom URValue at level 0) : ursus_scope.
End DFromGiverFuncs .

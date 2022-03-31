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

Require Import KWDPool.DKWDPool.Ledger.
Require Import KWDPool.DKWDPool.ClassTypesNotations.
Require Import KWDPool.DKWDPool.ClassTypes.
Require Import KWDPool.DKWDPool.Functions.FuncSig.
Require Import KWDPool.DKWDPool.Functions.FuncNotations.


Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypesNotations.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypesNotations.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypesNotations.
(* 
Require Import Contracts.KWErrorConstants.KWErrors.Interface.
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

Section  DKWDPoolFuncs.

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


Definition isFundReady_ : public ( XBool  ) false .
  refine {{ return_ fund_ready_flag_ }}.
Defined. 
Definition isFundReady_right : URValue ( XBool  )  false :=
wrapURExpression (ursus_call_with_args λ0 isFundReady_ ).
Notation " 'isFundReady' '('  ')' " := 
(isFundReady_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition getBalance_ : public ( XUInteger128 ) false .
  refine {{ return_ balance_ }}.
Defined. 
Definition getBalance_right : URValue ( XUInteger128 )  false :=
wrapURExpression (ursus_call_with_args λ0 getBalance_ ).
Notation " 'getBalance' '('  ')' " := 
(getBalance_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition isInitialized_ : public ( XBool  ) false .
  refine {{ return_ initialized_ }}.
Defined. 
Definition isInitialized_right : URValue ( XBool  )  false :=
wrapURExpression (ursus_call_with_args λ0 isInitialized_ ).
Notation " 'isInitialized' '('  ')' " := 
(isInitialized_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition check_fund : modifier .
unfold_mod.
  refine {{ require_((int_sender() == fund_address_), KWErrors.error_not_my_fund) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_fund  {_} {_}.

Definition check_init : modifier .
unfold_mod.
  refine {{ require_(initialized_, KWErrors.error_not_initialized) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_init  {_} {_}.

Definition onVoteAccept_ : external PhantomType true .
  refine (check_init  _) .
  refine (check_fund  _) .
  refine {{ return_ {} }}.
Defined. 
Definition onVoteAccept_left {R  } 
 : UExpression R  true  :=
wrapULExpression (ursus_call_with_args λ0 onVoteAccept_  ).
Notation " 'onVoteAccept' '('  ')' " := 
(onVoteAccept_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition onVoteReject_ (voting_id :  XUInteger8 ): external PhantomType true .
  refine (check_init  _) .
  refine (check_fund  _) .
  (* TODO *)
  (* refine {{ voting_bitmap_ &= ( XUInteger256 ((β #{1})) << #{voting_id}) ~ ; { _ } }}.  *)
  refine {{ return_ {} }}.
Defined. 
Definition onVoteReject_left {R b0 } 
(voting_id: URValue  XUInteger8  b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 onVoteReject_ voting_id ).
Notation " 'onVoteReject' '(' voting_id ')' " := 
(onVoteReject_left voting_id )  
(in custom ULValue at level 0 , 
voting_id custom URValue at level 0) : ursus_scope.

Definition check_owner : modifier .
unfold_mod.
  refine {{ require_((msg_pubkey() != (β #{0})), KWErrors.error_not_external_message) ; { _ } }}. 
  refine {{ require_((tvm_pubkey() == msg_pubkey()), KWErrors.error_not_my_pubkey) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_owner  {_} {_}.

Definition vote_ (choice :  XBool  ) (voting_id :  XUInteger8 ) (code_hash :  XUInteger256 ): external PhantomType true .
  refine (check_init  _) .
  refine (check_owner  _) .
  refine {{ require_((tvm_balance() >= (KWMessages.VOTING_FEE + ((β #{2}) * KWMessages.EPSILON_BALANCE))), KWErrors.error_balance_too_low) ; { _ } }}. 
  (* TODO приведение типов, однако если поменять тип voting_id не будет работать строчка 246 *)
  (* refine {{ require_(((voting_bitmap_ & ( XUInteger256 ((β #{1})) << #{voting_id})) == (β #{0})), KWErrors.error_already_voted) ; { _ } }}.  *)
  refine {{ tvm_accept() ; { _ } }}. 
  (* TODO *)
  (* ORIGINAL voting_bitmap_ |= uint256(1) << voting_id; *)
  (* refine {{ voting_bitmap_ |= (  ((β #{1})) << #{voting_id}) ; { _ } }}.  *)
  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        (KWMessages.VOTING_FEE + KWMessages.EPSILON_BALANCE) ⇒ { Messsage_ι_value};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.vote(tvm_pubkey(), nonce_, #{choice}, quant_, #{voting_id}, #{code_hash}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition vote_left {R b0 b1 b2 } 
(choice: URValue  XBool   b0 ) 
(voting_id: URValue  XUInteger8  b1 ) 
(code_hash: URValue  XUInteger256  b2 ) 
 : UExpression R (orb(orb(orb true b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ3 vote_ choice voting_id code_hash ).
Notation " 'vote' '(' choice ',' voting_id ',' code_hash ')' " := 
(vote_left choice voting_id code_hash )  
(in custom ULValue at level 0 , 
choice custom URValue at level 0, 
voting_id custom URValue at level 0, 
code_hash custom URValue at level 0) : ursus_scope.

Definition returnExtraFunds_ (address_to :  address  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  new 'delta : (  XUInteger128  ) @ "delta"  := ((tvm_balance() - balance_) - KWMessages.KWD_MIN_BALANCE) ; { _ } }}. 
  refine {{  if ( (!{delta} > KWMessages.EPSILON_BALANCE) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ tvm_transfer(#{address_to}, !{delta}, TRUE, (β #{1}))  }}. 

  refine {{ return_ {} }}.
Defined. 
Definition returnExtraFunds_left {R b0 } 
(address_to: URValue  address   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 returnExtraFunds_ address_to ).
Notation " 'returnExtraFunds' '(' address_to ')' " := 
(returnExtraFunds_left address_to )  
(in custom ULValue at level 0 , 
address_to custom URValue at level 0) : ursus_scope.

Definition _sendFunds_ (address_to :  address  ): internal PhantomType false .
  refine {{  if ( (balance_ > (β #{0})) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ tvm_transfer(#{address_to}, balance_, TRUE, (β #{1}))  }}. 

  refine {{ suicide_(final_address_ -> get_default () ) ; { _ } }}. 
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

Definition returnFunds_ (address_to :  address  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((#{address_to} != tvm_myaddr()), KWErrors.error_return_address_is_mine) ; { _ } }}. 
  refine {{ require_(((tvm_now() > unlock_time_) \\ (~ ( initialized_))), KWErrors.error_time_too_early) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ ( * final_address_ ) := (#{address_to}) ; { _ } }}. 
  refine {{ _sendFunds(#{address_to}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition returnFunds_left {R b0 } 
(address_to: URValue  address   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 returnFunds_ address_to ).
Notation " 'returnFunds' '(' address_to ')' " := 
(returnFunds_left address_to )  
(in custom ULValue at level 0 , 
address_to custom URValue at level 0) : ursus_scope.

Definition packParams_ (code :  cell_  ): internal ( cell_  ) false .
  refine {{  new 'main_builder : ( builder_  ) @ "main_builder" := builder() ; { _ } }}. 
  (* TODO *)
  refine {{ {main_builder} := !{main_builder} -> store ( σ lock_time_ )
         -> store ( σ unlock_time_ )
         -> store ( σ quant_ )
         -> store ( σ farm_rate_ )
         -> store ( σ kwf_lock_time_) ; { _ } }}.  
  refine {{  new 'static_builder : ( builder_  ) @ "static_builder" := builder() ; { _ } }}. 
  (* TODO *)
  refine {{ {static_builder} := !{static_builder} -> store ( σ tvm_pubkey() )
         -> store ( σ fund_address_ )
         -> store ( σ nonce_) ; { _ } }}.  
  refine {{  new 'dyn_builder : ( builder_  ) @ "dyn_builder" := builder() ; { _ } }}. 
  refine {{ {dyn_builder} := !{dyn_builder} -> store ( σ initialized_ )
         -> store ( σ balance_ )
         -> store ( σ final_address_ )
         -> store ( σ fund_ready_flag_ )
         -> store ( σ init_time_ )
         -> store ( σ deposit_time_) ; { _ } }}.  
  refine {{ {main_builder} := !{main_builder} -> stref (!{static_builder} -> make_cell ()) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> stref (!{dyn_builder} -> make_cell ()) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> stref (#{code}) ; { _ } }}. 
  refine {{ return_ !{main_builder} -> make_cell() }}.
Defined. 
Definition packParams_right {b0}
(code: URValue  cell_   b0 ) : URValue ( cell_  )  b0  :=
wrapURExpression (ursus_call_with_args λ1 packParams_ code).
Notation " 'packParams' '(' code ')' " := 
(packParams_right code)  
(in custom URValue at level 0 , 
code custom URValue at level 0) : ursus_scope.

Definition sendFunds_ (code :  cell_  ): external PhantomType true .
  refine (check_init  _) .
  refine (check_fund  _) .
  refine {{ require_(fund_ready_flag_, KWErrors.error_fund_ready_not_set) ; { _ } }}. 
  refine {{ require_(final_address_ != {} , KWErrors.error_final_address_not_set) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= ((int_value() + balance_) + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IKWFundPtr[[ fund_address_ ]] with 
      [$ 
        (balance_ + int_value()) ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFund.sendKWDPoolParams(tvm_pubkey(), nonce_, packParams(#{code})) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition sendFunds_left {R b0 } 
(code: URValue  cell_   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 sendFunds_ code ).
Notation " 'sendFunds' '(' code ')' " := 
(sendFunds_left code )  
(in custom ULValue at level 0 , 
code custom URValue at level 0) : ursus_scope.

Definition acknowledgeFunds_ : external PhantomType true .
  refine (check_init  _) .
  refine (check_fund  _) .
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ tvm_transfer(int_sender(), int_value(), FALSE, (β #{1})) ; { _ } }}. 
  refine {{ suicide_(final_address_ -> get_default () ) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition acknowledgeFunds_left {R  } 
 : UExpression R  true  :=
wrapULExpression (ursus_call_with_args λ0 acknowledgeFunds_  ).
Notation " 'acknowledgeFunds' '('  ')' " := 
(acknowledgeFunds_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition setFinalAddress_ (final_address :  address  ): external PhantomType true .
  refine (check_init  _) .
  refine (check_owner  _) .
  refine {{ require_((tvm_balance() >= (balance_ + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  (* TODO *)
  (* refine {{ final_address_.set(#{final_address}) ; { _ } }}.  *)
  refine {{ final_address_ -> set(#{final_address}) ; { _ } }}.  
  refine {{ return_ {} }}.
Defined. 
Definition setFinalAddress_left {R b0 } 
(final_address: URValue  address   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 setFinalAddress_ final_address ).
Notation " 'setFinalAddress' '(' final_address ')' " := 
(setFinalAddress_left final_address )  
(in custom ULValue at level 0 , 
final_address custom URValue at level 0) : ursus_scope.

Definition notifyParticipant_ (giveup :  XBool  ) (investors_adj_summa_ :  XUInteger128 ) (summa_givers :  XUInteger128 ): external PhantomType true .
  refine (check_init  _) .
  refine (check_fund  _) .
  refine {{ require_(((tvm_now() >= lock_time_) && (tvm_now() <= unlock_time_)), KWErrors.error_time_not_inside) ; { _ } }}. 
  refine {{ require_((~ ( fund_ready_flag_)), KWErrors.error_fund_ready_set) ; { _ } }}. 
  refine {{ require_(final_address_ != {} , KWErrors.error_final_address_not_set) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= ((int_value() + balance_) + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ if ( (balance_ == (β #{0})) ) then { {_:UExpression _ false} } else { {_} } ; { _ } }}.
  refine {{ suicide_(final_address_ -> get_default () )  }}. 

  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        int_value() ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.acknowledgeFinalizeLeft(tvm_pubkey(), nonce_) ; { _ } }}. 
  refine {{ if ( #{giveup} ) then { {_:UExpression _ false} } else { {_} }  }}.
  refine {{ _sendFunds(final_address_ -> get_default () )  }}. 

  refine {{ fund_ready_flag_ := TRUE ; { _ } }}. 
  refine {{  if ( (#{investors_adj_summa_} > #{summa_givers}) ) then { {_:UExpression _ false} }  }}.
  refine {{  new 'extra : (  XUInteger128  ) @ "extra"  := math.muldiv(balance_, (#{investors_adj_summa_} - #{summa_givers}), #{investors_adj_summa_}) ; { _ } }}. 
  refine {{ balance_ -= !{extra} ; { _ } }}. 
  refine {{ tvm_transfer(final_address_ -> get_default () , !{extra}, TRUE, (β #{1}))  }}. 



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
  refine (check_init  _) .
  refine {{  if ( (balance_ == (β #{0})) ) then { {_:UExpression _ true} } ; { _ } }}.
  refine {{ require_((int_value() >= quant_), KWErrors.error_msg_value_too_low) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= ((int_value() + KWMessages.GAS_FOR_FUND_MESSAGE) + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ balance_ := quant_ ; { _ } }}. 
  refine {{ deposit_time_ := tvm_now() ; { _ } }}. 
  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        KWMessages.GAS_FOR_FUND_MESSAGE ⇒ { Messsage_ι_value};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.notifyLeft(tvm_pubkey(), nonce_, balance_, math.muldiv(balance_,ι farm_rate_, (β #{100}))) ; { _ } }}.
      lia. (*TODO farm_rate_!*) 
  refine {{  if ( (~ ( final_address_ != {} )) ) then { {_:UExpression _ false} } ; { _ } }}.
  (* TODO *)
  refine {{ final_address_ -> set(int_sender())  }}.  

  refine {{  new 'extra : (  XUInteger128  ) @ "extra"  := (int_value() - quant_) ; { _ } }}. 
  refine {{  if ( (!{extra} >= KWMessages.EPSILON_BALANCE) ) then { {_:UExpression _ false} }  }}.
  refine {{ tvm_transfer(int_sender(), !{extra}, TRUE, KWMessages.DEFAULT_MSG_FLAGS)  }}. 


  refine {{ return_ {} }}.
Defined. 
Definition receive_left {R  } 
 : UExpression R  true  :=
wrapULExpression (ursus_call_with_args λ0 receive_  ).
Notation " 'receive' '('  ')' " := 
(receive_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition initialize_ (lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) (quant :  XUInteger128 ) (rate :  XUInteger8 ) (kwf_lock_time :  XUInteger32 ): external PhantomType true .
  refine (check_fund  _) .
  refine {{ require_((~ ( initialized_)), KWErrors.error_initialized) ; { _ } }}. 
  refine {{ require_((tvm_now() < #{lock_time}), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ quant_ := #{quant} ; { _ } }}. 
  refine {{ lock_time_ := #{lock_time} ; { _ } }}. 
  refine {{ unlock_time_ := #{unlock_time} ; { _ } }}. 
  refine {{ farm_rate_ := #{rate} ; { _ } }}. 
  refine {{ kwf_lock_time_ := #{kwf_lock_time} ; { _ } }}. 
  refine {{ initialized_ := TRUE ; { _ } }}. 
  refine {{ init_time_ := tvm_now() ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition initialize_left {R b0 b1 b2 b3 b4 } 
(lock_time: URValue  XUInteger32  b0 ) 
(unlock_time: URValue  XUInteger32  b1 ) 
(quant: URValue  XUInteger128  b2 ) 
(rate: URValue  XUInteger8  b3 ) 
(kwf_lock_time: URValue  XUInteger32  b4 ) 
 : UExpression R (orb(orb(orb(orb(orb true b4)b3)b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ5 initialize_ lock_time unlock_time quant rate kwf_lock_time ).
Notation " 'initialize' '(' lock_time ',' unlock_time ',' quant ',' rate ',' kwf_lock_time ')' " := 
(initialize_left lock_time unlock_time quant rate kwf_lock_time )  
(in custom ULValue at level 0 , 
lock_time custom URValue at level 0, 
unlock_time custom URValue at level 0, 
quant custom URValue at level 0, 
rate custom URValue at level 0, 
kwf_lock_time custom URValue at level 0) : ursus_scope.

Definition constructor_ (final_address :  XMaybe  (  address  ) ): public PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((tvm_balance() >= (KWMessages.KWD_MIN_BALANCE + KWMessages.GAS_FOR_FUND_MESSAGE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((~ ( fund_address_== {})), KWErrors.error_fund_not_set) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ IBlankPtr[[ fund_address_ ]] with 
      [$ 
        KWMessages.GAS_FOR_FUND_MESSAGE ⇒ { Messsage_ι_value};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IBlank.isFundReady(tvm_pubkey(), nonce_) ; { _ } }}. 
  refine {{ balance_ := (β #{0}) ; { _ } }}. 
  refine {{ final_address_ := #{final_address} ; { _ } }}. 
  refine {{ voting_flag_ := FALSE ; { _ } }}. 
  refine {{ fund_ready_flag_ := FALSE ; { _ } }}. 
  refine {{ initialized_ := FALSE ; { _ } }}. 
  refine {{ lock_time_ := (β #{0}) ; { _ } }}. 
  refine {{ unlock_time_ := (β #{0}) ; { _ } }}. 
  refine {{ quant_ := (β #{0}) ; { _ } }}. 
  refine {{ farm_rate_ := (β #{0}) ; { _ } }}. 
  refine {{ kwf_lock_time_ := (β #{0}) ; { _ } }}. 
  refine {{ init_time_ := (β #{0}) ; { _ } }}. 
  refine {{ deposit_time_ := (β #{0}) ; { _ } }}. 
  refine {{ voting_bitmap_ := (β #{0}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition constructor_left {R b0 } 
(final_address: URValue  (XMaybe  (  address  ))  b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 constructor_ final_address ).
Notation " 'constructor' '(' final_address ')' " := 
(constructor_left final_address )  
(in custom ULValue at level 0 , 
final_address custom URValue at level 0) : ursus_scope.
End DKWDPoolFuncs .

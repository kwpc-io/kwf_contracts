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

Require Import Blank.DBlank.Ledger.
Require Import Blank.DBlank.ClassTypesNotations.
Require Import Blank.DBlank.ClassTypes.
Require Import Blank.DBlank.Functions.FuncSig.
Require Import Blank.DBlank.Functions.FuncNotations.


Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypesNotations.

Require Import Contracts.FromGiver.DFromGiver.Interface.
Require Import Contracts.FromGiver.DFromGiver.ClassTypes.
Require Import Contracts.FromGiver.DFromGiver.ClassTypesNotations.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypesNotations.

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

Section  DBlankFuncs.

Context `{KWErrorsCommonErrors}.
(*Context `{KWErrorsCommonConsts}*) 
(*Context `{KWMessagesCommonConsts}*)

Context {KWErrors_ι_voting_time_too_long_  :  ErrorType  }. 
Notation " 'KWErrors.voting_time_too_long' " := (sInject KWErrors_ι_voting_time_too_long_) (in custom URValue at level 0) : ursus_scope. 
Context {KWErrors_ι_voting_time_too_low_  :  ErrorType  }. 
Notation " 'KWErrors.voting_time_too_low' " := (sInject KWErrors_ι_voting_time_too_low_) (in custom URValue at level 0) : ursus_scope. 
Context {KWErrors_ι_voting_fee_too_low_  :  ErrorType  }. 
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

(* WARNING они были типа uint256! *)
Definition getTimes_ : public ( XUInteger32  #  XUInteger32  #  XUInteger32 ) false .
  refine {{ return_ [ [ lock_time_, unlock_time_ ], kwf_lock_time_ ] }}.
Defined. 
Definition getTimes_right : URValue ( XUInteger32  #  XUInteger32  #  XUInteger32 )  false :=
wrapURExpression (ursus_call_with_args λ0 getTimes_ ).
Notation " 'getTimes' '('  ')' " := 
(getTimes_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition getInvestorsNumbers_ : public ( XUInteger32  #  XUInteger32 ) false .
  refine {{ return_ [ num_investors_sent_, num_investors_received_ ] }}.
Defined. 
Definition getInvestorsNumbers_right : URValue ( XUInteger32  #  XUInteger32 )  false :=
wrapURExpression (ursus_call_with_args λ0 getInvestorsNumbers_ ).
Notation " 'getInvestorsNumbers' '('  ')' " := 
(getInvestorsNumbers_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition getGiversSum_ : public ( XUInteger128 ) false .
  refine {{ return_ givers_summa_ }}.
Defined. 
Definition getGiversSum_right : URValue ( XUInteger128 )  false :=
wrapURExpression (ursus_call_with_args λ0 getGiversSum_ ).
Notation " 'getGiversSum' '('  ')' " := 
(getGiversSum_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition getInvestorsSum_ : public ( XUInteger128  #  XUInteger128 ) false .
  refine {{ return_ [ investors_adj_summa_, investors_summa_ ] }}.
Defined. 
Definition getInvestorsSum_right : URValue ( XUInteger128  #  XUInteger128 )  false :=
wrapURExpression (ursus_call_with_args λ0 getInvestorsSum_ ).
Notation " 'getInvestorsSum' '('  ')' " := 
(getInvestorsSum_right )  
(in custom URValue at level 0 ) : ursus_scope.

Definition check_owner : modifier .
unfold_mod.
  refine {{ require_((msg_pubkey() != (β #{0})), KWErrors.error_not_external_message) ; { _ } }}. 
  refine {{ require_((tvm_pubkey() == msg_pubkey()), KWErrors.error_not_my_pubkey) ; { _ } }}. 
  refine u.
Defined. 
Arguments check_owner  {_} {_}.
Print tvm_transfer.
Definition killBlank_ (address_to :  address  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((#{address_to} != tvm_myaddr()), KWErrors.error_return_address_is_mine) ; { _ } }}. 
  refine {{ require_((tvm_now() > unlock_time_), KWErrors.error_time_too_early) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ suicide_(#{address_to}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition killBlank_left {R b0 } 
(address_to: URValue  address   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 killBlank_ address_to ).
Notation " 'killBlank' '(' address_to ')' " := 
(killBlank_left address_to )  
(in custom ULValue at level 0 , 
address_to custom URValue at level 0) : ursus_scope.

Definition onCodeUpgrade_ (cell :  cell_  ): private PhantomType false .
  refine {{ return_ {} }}.
Defined. 
Definition onCodeUpgrade_left {R b0 } 
(cell: URValue  cell_   b0 ) 
 : UExpression R (orb false b0) :=
wrapULExpression (ursus_call_with_args λ1 onCodeUpgrade_ cell ).
Notation " 'onCodeUpgrade' '(' cell ')' " := 
(onCodeUpgrade_left cell )  
(in custom ULValue at level 0 , 
cell custom URValue at level 0) : ursus_scope.


Definition finalizeVoting_ : internal PhantomType false .
  refine {{  if ( (tvm_now() <= (voting_start_time_ + voting_time_)) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ return_ {} }}.

  refine {{  new 'y : (  XUInteger128  ) @ "y"  := voted_for_ ; { _ } }}. 
  refine {{  new 'n : (  XUInteger128  ) @ "n"  := voted_against_ ; { _ } }}. 
  refine {{  new 't : (  XUInteger128  ) @ "t"  := investors_summa_ ; { _ } }}. 
  (* TODO *)
  
  refine {{ if ( (!{y} >= (((β #{1}) + (!{t} / (β #{10}))  ) + ((!{n} * ((!{t} / (β #{2})) - (!{t} / (β #{10})))) / (!{t} / (β #{2}))  ))  ) ) then { {_:UExpression _ false} }  else { {_:UExpression _ false} }  ; {_:UExpression _ false} }}.
  refine {{ voting_result_ -> set(TRUE)  }}.
  refine {{ voting_result_ -> set(FALSE)  }}.
  refine {{ voting_id_ := voting_id_ + β #{1}; { _ } }}.
  refine {{ return_ {} }}.
Defined. 
Definition finalizeVoting_left {R  } 
 : UExpression R  false  :=
wrapULExpression (ursus_call_with_args λ0 finalizeVoting_  ).
Notation " 'finalizeVoting' '('  ')' " := 
(finalizeVoting_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

Definition startVoting_ (voting_time :  XUInteger32 ) (code_hash :  XUInteger256 ): external PhantomType true .
  refine (check_owner  _) .
  (* TODO  *)
  refine {{ require_((#{voting_time} >= KWMessages.MIN_VOTING_TIME), KWErrors.voting_time_too_low) ; { _ } }}.  
  refine {{ require_((tvm_now() >= lock_time_), KWErrors.error_time_too_early) ; { _ } }}. 
  (* TODO  *)
  refine {{ require_(((((tvm_now() + #{voting_time}) + KWMessages.TIME_FOR_SETCODE_PREPARE) + KWMessages.TIME_FOR_FUNDS_COLLECTING) < unlock_time_), KWErrors.voting_time_too_long) ; { _ } }}.  
  refine {{ require_((num_investors_received_ >= num_investors_sent_), KWErrors.error_not_all_ack) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  if ( (~ ( voting_result_ != {})) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ finalizeVoting( )  }}. 

  refine {{  if ( ((~ ( voting_result_ != {})) \\ (voting_result_ -> get_default ()  == TRUE)) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ return_ {} }}.

  refine {{ voted_for_ := (β #{0}) ; { _ } }}. 
  refine {{ voted_against_ := (β #{0}) ; { _ } }}. 
  refine {{ voting_start_time_ := tvm_now() ; { _ } }}. 
  refine {{ voting_time_ := #{voting_time} ; { _ } }}. 
  (* TODO  *)
  (* refine {{ voting_result_.reset() ; { _ } }}.  *)
  refine {{ voting_result_ -> set({}) ; { _ } }}.

  refine {{ voting_code_hash_ := #{code_hash} ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition startVoting_left {R b0 b1 } 
(voting_time: URValue  XUInteger32  b0 ) 
(code_hash: URValue  XUInteger256  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 startVoting_ voting_time code_hash ).
Notation " 'startVoting' '(' voting_time ',' code_hash ')' " := 
(startVoting_left voting_time code_hash )  
(in custom ULValue at level 0 , 
voting_time custom URValue at level 0, 
code_hash custom URValue at level 0) : ursus_scope.

Definition tryEarlyComplete_ : internal PhantomType false .
  refine {{  if ( (~ ( voting_result_ != {})) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ if ( (((β #{2}) * voted_for_) > investors_summa_) ) then { {_:UExpression _ false} } else { {_} }  }}.
  (* TODO  *)
  (* refine {{ voting_result_.set(TRUE) ; { _ } }}.  *)
  refine {{ voting_result_ -> set(TRUE) ; { _ } }}.  
  (* refine {{ voting_id_ ++  }}.  *)
  refine {{ voting_id_ := voting_id_ + β #{1} }}.

  refine {{  if ( (((β #{2}) * voted_against_) > investors_summa_) ) then { {_:UExpression _ false} }  }}.
  (* TODO  *)
  (* refine {{ voting_result_.set(FALSE) ; { _ } }}. 
  refine {{ voting_id_ ++  }}.  *)
  refine {{ voting_result_ -> set(FALSE) ; { _ }  }}. 
  refine {{ voting_id_ := voting_id_ + β #{1} }}.

  refine {{ return_ {} }}.
(*   refine {{ return_ {} }}.
  refine {{ return_ {} }}.
 *)Defined. 
Definition tryEarlyComplete_left {R  } 
 : UExpression R  false  :=
wrapULExpression (ursus_call_with_args λ0 tryEarlyComplete_  ).
Notation " 'tryEarlyComplete' '('  ')' " := 
(tryEarlyComplete_left  )  
(in custom ULValue at level 0 ) : ursus_scope.

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

Definition vote_ (pk :  XUInteger256 ) (nonce :  XUInteger256 ) (choice :  XBool  ) (sum :  XUInteger128 ) (voting_id :  XUInteger8 ) (code_hash :  XUInteger256 ): external PhantomType true .
  refine (check_investor pk nonce _) .
  (* TODO  *)
  refine {{ require_((int_value() >= KWMessages.VOTING_FEE), KWErrors.voting_fee_too_low) ; { _ } }}.  
  refine {{  if ( voting_result_ != {} ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        FALSE ⇒ { Messsage_ι_bounce};
        (β #{64}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.onVoteReject(#{voting_id}) ; { _ } }}. 
  refine {{ return_ {} }}.

  refine {{  if ( ((tvm_now() < voting_start_time_) \\ (tvm_now() > (voting_start_time_ + voting_time_))) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        FALSE ⇒ { Messsage_ι_bounce};
        (β #{64}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.onVoteReject(#{voting_id}) ; { _ } }}. 
  refine {{ return_ {} }}.

  refine {{  if ( (#{code_hash} != voting_code_hash_) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        FALSE ⇒ { Messsage_ι_bounce};
        (β #{64}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.onVoteReject(#{voting_id}) ; { _ } }}. 
  refine {{ return_ {} }}.
  (* TODO  *)
  refine {{  if ( (#{voting_id} != voting_id_) ) then { {_:UExpression _ false} } ; { _ } }}. 
  (* Actually work  *)
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        FALSE ⇒ { Messsage_ι_bounce};
        (β #{64}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.onVoteReject(#{voting_id}) ; { _ } }}. 
  refine {{ return_ {} }}. 

  refine {{ if ( #{choice} ) then { {_:UExpression _ false} } else { {_} } ; { _ } }}.
  refine {{ voted_for_ += #{sum}  }}. 

  refine {{ voted_against_ += #{sum}  }}. 

  refine {{ tryEarlyComplete( ) ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        FALSE ⇒ { Messsage_ι_bounce};
        (β #{64}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.onVoteAccept( ) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition vote_left {R b0 b1 b2 b3 b4 b5 } 
(pk: URValue  XUInteger256  b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
(choice: URValue  XBool   b2 ) 
(sum: URValue  XUInteger128  b3 ) 
(voting_id: URValue  XUInteger8  b4 ) 
(code_hash: URValue  XUInteger256  b5 ) 
 : UExpression R (orb(orb(orb(orb(orb(orb true b5)b4)b3)b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ6 vote_ pk nonce choice sum voting_id code_hash ).
Notation " 'vote' '(' pk ',' nonce ',' choice ',' sum ',' voting_id ',' code_hash ')' " := 
(vote_left pk nonce choice sum voting_id code_hash )  
(in custom ULValue at level 0 , 
pk custom URValue at level 0, 
nonce custom URValue at level 0, 
choice custom URValue at level 0, 
sum custom URValue at level 0, 
voting_id custom URValue at level 0, 
code_hash custom URValue at level 0) : ursus_scope.

Definition setFundCode_ (code :  cell_  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_(((tvm_now() + KWMessages.TIME_FOR_FUNDS_COLLECTING) <= unlock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.RESPAWN_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_hash(#{code}) == voting_code_hash_), KWErrors.error_code_not_correct) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  if ( (~ ( voting_result_ != {})) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ finalizeVoting( )  }}. 

  refine {{  if ( ((~ ( voting_result_ != {})) \\ (~ ( voting_result_ -> get_default () ))) ) then { {_:UExpression _ false} } ; { _ } }}.
  refine {{ return_ {} }}.

  refine {{  new 'main_builder : ( builder_  ) @ "main_builder" := builder() ; { _ } }}. 
  (* TODO  *)
  refine {{ {main_builder} := !{main_builder} -> store ( σ kwdpool_code_hash_ )
                                              -> store ( σ kwdpool_code_depth_ )
                                              -> store ( σ fromgiver_code_hash_ )
                                              -> store ( σ fromgiver_code_depth_) ; { _ } }}. 
  refine {{  new 'dyn_builder : ( builder_  ) @ "dyn_builder" := builder() ; { _ } }}. 
  (* TODO *)
  refine {{ {dyn_builder} := !{dyn_builder} -> store ( σ givers_summa_ )
         -> store ( σ investors_adj_summa_ )
         -> store ( σ investors_summa_ )
         -> store ( σ min_summa_ )
         -> store ( σ max_summa_ )
         -> store ( σ num_investors_sent_ )
         -> store ( σ num_from_givers_) ; { _ } }}.  
  refine {{  new 'static_builder : ( builder_  ) @ "static_builder" := builder() ; { _ } }}. 
  refine {{ {static_builder} := !{static_builder} -> store ( σ tvm_pubkey() )
         -> store ( σ lock_time_ )
         -> store ( σ unlock_time_ )
         -> store ( σ farm_rate_ )
         -> store ( σ kwf_lock_time_ )
         -> store ( σ quant_ )
         -> store ( σ nonce_) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> stref ( !{dyn_builder} -> make_cell () ) ; { _ } }}. 
  refine {{ {main_builder} := !{main_builder} -> stref ( !{static_builder} -> make_cell () ) ; { _ } }}.  
  refine {{ tvm_setCode(#{code}) ; { _ } }}. 
  refine {{ tvm_setCurrentCode(#{code}) ; { _ } }}. 
  refine {{ onCodeUpgrade(!{main_builder} -> make_cell()) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition setFundCode_left {R b0 } 
(code: URValue  cell_   b0 ) 
 : UExpression R (orb true b0) :=
wrapULExpression (ursus_call_with_args λ1 setFundCode_ code ).
Notation " 'setFundCode' '(' code ')' " := 
(setFundCode_left code )  
(in custom ULValue at level 0 , 
code custom URValue at level 0) : ursus_scope.

Definition finalize_ (force_giveup :  XBool  ) (addr :  address  ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_(((tvm_now() >= lock_time_) && (tvm_now() <= unlock_time_)), KWErrors.error_time_not_inside) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= (KWMessages.GAS_FOR_PARTICIPANT_MESSAGE + KWMessages.EPSILON_BALANCE)), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((num_investors_received_ < num_investors_sent_), KWErrors.error_already_all_ack) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  new 'giveup : (  XBool   ) @ "giveup"  := ((min(investors_summa_, givers_summa_) < min_summa_) \\ #{force_giveup}) ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ #{addr} ]] with 
      [$ 
        KWMessages.GAS_FOR_PARTICIPANT_MESSAGE ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        (β #{1}) ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.notifyParticipant(!{giveup}, investors_adj_summa_, givers_summa_) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition finalize_left {R b0 b1 } 
(force_giveup: URValue  XBool   b0 ) 
(addr: URValue  address   b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 finalize_ force_giveup addr ).
Notation " 'finalize' '(' force_giveup ',' addr ')' " := 
(finalize_left force_giveup addr )  
(in custom ULValue at level 0 , 
force_giveup custom URValue at level 0, 
addr custom URValue at level 0) : ursus_scope.

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

Definition acknowledgeFinalizeRight_ (giver :  address  ) (nonce :  XUInteger256 ) (dead_giver :  XBool  ): external PhantomType true .
  refine (check_giver giver nonce _) .
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  if ( #{dead_giver} ) then { {_:UExpression _ false} } ; { _ } }}.
  (* TODO *)
  (* refine {{ num_from_givers_ --  }}. 
  refine {{ num_investors_received_ ++ ; { _ } }}.  *)
  refine {{ num_from_givers_ := num_from_givers_ - β #{1} }}.
  refine {{ num_investors_received_ := num_investors_received_ + β #{1} ; { _ }  }}.

  refine {{ return_ {} }}.
Defined. 
Definition acknowledgeFinalizeRight_left {R b0 b1 b2 } 
(giver: URValue  address   b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
(dead_giver: URValue  XBool   b2 ) 
 : UExpression R (orb(orb(orb true b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ3 acknowledgeFinalizeRight_ giver nonce dead_giver ).
Notation " 'acknowledgeFinalizeRight' '(' giver ',' nonce ',' dead_giver ')' " := 
(acknowledgeFinalizeRight_left giver nonce dead_giver )  
(in custom ULValue at level 0 , 
giver custom URValue at level 0, 
nonce custom URValue at level 0, 
dead_giver custom URValue at level 0) : ursus_scope.

Definition acknowledgeFinalizeLeft_ (pk :  XUInteger256 ) (nonce :  XUInteger256 ): external PhantomType true .
  refine (check_investor pk nonce _) .
  refine {{ tvm_accept() ; { _ } }}. 
  (* TODO *)
  (* refine {{ num_investors_received_ ++ ; { _ } }}.  *)
  refine {{ num_investors_received_ := num_investors_received_ + β #{1} ; { _ }  }}.
  refine {{ return_ {} }}.
Defined. 
Definition acknowledgeFinalizeLeft_left {R b0 b1 } 
(pk: URValue  XUInteger256  b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 acknowledgeFinalizeLeft_ pk nonce ).
Notation " 'acknowledgeFinalizeLeft' '(' pk ',' nonce ')' " := 
(acknowledgeFinalizeLeft_left pk nonce )  
(in custom ULValue at level 0 , 
pk custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition notifyRight_ (giver :  address  ) (nonce :  XUInteger256 ) (balance :  XUInteger128 ) (income :  XUInteger128 ): external PhantomType true .
  refine (check_giver giver nonce _) .
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ givers_summa_ += #{income} ; { _ } }}. 
  (* refine {{ #{balance} := #{balance} ; { _ } }}.  *)
  refine {{ tvm_transfer(int_sender(), (β #{0}), FALSE, KWMessages.MSG_VALUE_BUT_FEE_FLAGS) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition notifyRight_left {R b0 b1 b2 b3 } 
(giver: URValue  address   b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
(balance: URValue  XUInteger128  b2 ) 
(income: URValue  XUInteger128  b3 ) 
 : UExpression R (orb(orb(orb(orb true b3)b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ4 notifyRight_ giver nonce balance income ).
Notation " 'notifyRight' '(' giver ',' nonce ',' balance ',' income ')' " := 
(notifyRight_left giver nonce balance income )  
(in custom ULValue at level 0 , 
giver custom URValue at level 0, 
nonce custom URValue at level 0, 
balance custom URValue at level 0, 
income custom URValue at level 0) : ursus_scope.

Definition acknowledgeDeploy_ (giver :  address  ) (nonce :  XUInteger256 ): external PhantomType true .
  refine (check_giver giver nonce _) .
  refine {{ tvm_accept() ; { _ } }}. 
  (* TODO *)
  (* refine {{ num_investors_sent_ ++ ; { _ } }}. 
  refine {{ num_from_givers_ ++ ; { _ } }}.  *)
  refine {{ num_investors_sent_ := num_investors_sent_ + β #{1} ; { _ }  }}.
  refine {{ num_from_givers_ := num_from_givers_ + β #{1} ; { _ }  }}.
  refine {{ can_change_fromgiver_code_ := FALSE ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition acknowledgeDeploy_left {R b0 b1 } 
(giver: URValue  address   b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 acknowledgeDeploy_ giver nonce ).
Notation " 'acknowledgeDeploy' '(' giver ',' nonce ')' " := 
(acknowledgeDeploy_left giver nonce )  
(in custom ULValue at level 0 , 
giver custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition deployFromGiver_ (code :  cell_  ) (giver :  address  ) (nonce :  XUInteger256 ): external ( address  ) true .
  refine (check_owner  _) .
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ require_((~ ( #{giver}== {})), KWErrors.error_giver_not_set) ; { _ } }}. 
  refine {{ require_((tvm_hash(#{code}) == fromgiver_code_hash_), KWErrors.error_not_my_code) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= (KWMessages.FG_MIN_BALANCE + ((β #{2}) * KWMessages.EPSILON_BALANCE))), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{  new 'dataCell : (  cell_   ) @ "dataCell"  := buildFromGiverDataInitCell(#{giver}, #{nonce}) ; { _ } }}. 
  refine {{  new 'stateInit : (  cell_   ) @ "stateInit"  := tvm_buildStateInit(#{code}, !{dataCell}, β #{0} ) ; { _ } }}. 
  refine {{  new 'fgaddr : (  address   ) @ "fgaddr"  := 
  new  |{ DFromGiverPtr }|  with 
        [$ (KWMessages.FG_MIN_BALANCE + KWMessages.EPSILON_BALANCE) 
                                ⇒ {DeployInit_ι_value}  ;
        !{stateInit} ⇒ {DeployInit_ι_stateInit}  $] 
        (lock_time_,unlock_time_); {_} }}.
  refine {{ return_ !{fgaddr} }}.
Defined. 
Definition deployFromGiver_right {b0 b1 b2}
(code: URValue  cell_   b0 ) 
(giver: URValue  address   b1 ) 
(nonce: URValue  XUInteger256  b2 ) : URValue ( address  ) (orb(orb (orb true b2) b1)b0) :=
wrapURExpression (ursus_call_with_args λ3 deployFromGiver_ code giver nonce).
Notation " 'deployFromGiver' '(' code ',' giver ',' nonce ')' " := 
(deployFromGiver_right code giver nonce)  
(in custom URValue at level 0 , 
code custom URValue at level 0, 
giver custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition notifyLeft_ (pk :  XUInteger256 ) (nonce :  XUInteger256 ) (balance :  XUInteger128 ) (adj_balance :  XUInteger128 ): external PhantomType true .
  refine (check_investor pk nonce _) .
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ investors_adj_summa_ += #{adj_balance} ; { _ } }}. 
  refine {{ investors_summa_ += #{balance} ; { _ } }}. 
  (* TODO *)
  (* refine {{ num_investors_sent_ ++ ; { _ } }}.  *)
  refine {{ num_investors_sent_ := num_investors_sent_ + β #{1} ; { _ }  }}.
  refine {{ tvm_transfer(int_sender(), (β #{0}), FALSE, KWMessages.MSG_VALUE_BUT_FEE_FLAGS) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition notifyLeft_left {R b0 b1 b2 b3 } 
(pk: URValue  XUInteger256  b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
(balance: URValue  XUInteger128  b2 ) 
(adj_balance: URValue  XUInteger128  b3 ) 
 : UExpression R (orb(orb(orb(orb true b3)b2)b1)b0) :=
wrapULExpression (ursus_call_with_args λ4 notifyLeft_ pk nonce balance adj_balance ).
Notation " 'notifyLeft' '(' pk ',' nonce ',' balance ',' adj_balance ')' " := 
(notifyLeft_left pk nonce balance adj_balance )  
(in custom ULValue at level 0 , 
pk custom URValue at level 0, 
nonce custom URValue at level 0, 
balance custom URValue at level 0, 
adj_balance custom URValue at level 0) : ursus_scope.

Definition isFundReady_ (pk :  XUInteger256 ) (nonce :  XUInteger256 ): external PhantomType true .
  refine (check_investor pk nonce _) .
  refine {{ can_change_kwdpool_code_ := FALSE ; { _ } }}. 
  refine {{ IKWFundParticipantPtr[[ int_sender() ]] with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        TRUE ⇒ { Messsage_ι_bounce};
        KWMessages.MSG_VALUE_BUT_FEE_FLAGS ⇒ { Messsage_ι_flags}
      $] ⤳ IKWFundParticipant.initialize(lock_time_, unlock_time_, quant_, farm_rate_, kwf_lock_time_) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition isFundReady_left {R b0 b1 } 
(pk: URValue  XUInteger256  b0 ) 
(nonce: URValue  XUInteger256  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 isFundReady_ pk nonce ).
Notation " 'isFundReady' '(' pk ',' nonce ')' " := 
(isFundReady_left pk nonce )  
(in custom ULValue at level 0 , 
pk custom URValue at level 0, 
nonce custom URValue at level 0) : ursus_scope.

Definition setKWDPoolCodeHash_ (code_hash :  XUInteger256 ) (code_depth :  XUInteger16 ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_(can_change_kwdpool_code_, KWErrors.error_cannot_change_code) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ kwdpool_code_hash_ := #{code_hash} ; { _ } }}. 
  refine {{ kwdpool_code_depth_ := #{code_depth} ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition setKWDPoolCodeHash_left {R b0 b1 } 
(code_hash: URValue  XUInteger256  b0 ) 
(code_depth: URValue  XUInteger16  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 setKWDPoolCodeHash_ code_hash code_depth ).
Notation " 'setKWDPoolCodeHash' '(' code_hash ',' code_depth ')' " := 
(setKWDPoolCodeHash_left code_hash code_depth )  
(in custom ULValue at level 0 , 
code_hash custom URValue at level 0, 
code_depth custom URValue at level 0) : ursus_scope.

Definition setFromGiverCodeHash_ (code_hash :  XUInteger256 ) (code_depth :  XUInteger16 ): external PhantomType true .
  refine (check_owner  _) .
  refine {{ require_(can_change_fromgiver_code_, KWErrors.error_cannot_change_code) ; { _ } }}. 
  refine {{ require_((tvm_balance() >= KWMessages.EPSILON_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ fromgiver_code_hash_ := #{code_hash} ; { _ } }}. 
  refine {{ fromgiver_code_depth_ := #{code_depth} ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition setFromGiverCodeHash_left {R b0 b1 } 
(code_hash: URValue  XUInteger256  b0 ) 
(code_depth: URValue  XUInteger16  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 setFromGiverCodeHash_ code_hash code_depth ).
Notation " 'setFromGiverCodeHash' '(' code_hash ',' code_depth ')' " := 
(setFromGiverCodeHash_left code_hash code_depth )  
(in custom ULValue at level 0 , 
code_hash custom URValue at level 0, 
code_depth custom URValue at level 0) : ursus_scope.

Definition constructor_ (min_summa :  XUInteger128 ) (max_summa :  XUInteger128 ): public PhantomType true .
  refine (check_owner  _) .
  refine {{ require_((tvm_balance() >= KWMessages.BLANK_MIN_BALANCE), KWErrors.error_balance_too_low) ; { _ } }}. 
  refine {{ require_((tvm_now() < lock_time_), KWErrors.error_time_too_late) ; { _ } }}. 
  refine {{ require_((#{min_summa} <= #{max_summa}), KWErrors.error_max_summa_less_min) ; { _ } }}. 
  refine {{ require_((lock_time_ < unlock_time_), KWErrors.error_unlock_time_less_lock) ; { _ } }}. 
  refine {{ require_((quant_ > (β #{0})), KWErrors.error_quant_not_set) ; { _ } }}. 
  refine {{ require_(((farm_rate_ > (β #{0})) && (farm_rate_ <= (β #{100}))), KWErrors.error_rate_not_set) ; { _ } }}. 
  refine {{ require_((kwf_lock_time_ > (β #{0})), KWErrors.error_kwf_lock_time_not_set) ; { _ } }}. 
  refine {{ tvm_accept() ; { _ } }}. 
  refine {{ givers_summa_ := (β #{0}) ; { _ } }}. 
  refine {{ investors_adj_summa_ := (β #{0}) ; { _ } }}. 
  refine {{ investors_summa_ := (β #{0}) ; { _ } }}. 
  refine {{ min_summa_ := #{min_summa} ; { _ } }}. 
  refine {{ max_summa_ := #{max_summa} ; { _ } }}. 
  refine {{ fromgiver_code_hash_ := (β #{0}) ; { _ } }}. 
  refine {{ kwdpool_code_hash_ := (β #{0}) ; { _ } }}. 
  refine {{ fromgiver_code_depth_ := (β #{0}) ; { _ } }}. 
  refine {{ kwdpool_code_depth_ := (β #{0}) ; { _ } }}. 
  refine {{ num_investors_sent_ := (β #{0}) ; { _ } }}. 
  refine {{ num_investors_received_ := (β #{0}) ; { _ } }}. 
  refine {{ can_change_kwdpool_code_ := TRUE ; { _ } }}. 
  refine {{ can_change_fromgiver_code_ := TRUE ; { _ } }}. 
  refine {{ num_from_givers_ := (β #{0}) ; { _ } }}. 
  refine {{ voted_for_ := (β #{0}) ; { _ } }}. 
  refine {{ voted_against_ := (β #{0}) ; { _ } }}. 
  refine {{ voting_start_time_ := (β #{0}) ; { _ } }}. 
  refine {{ voting_time_ := (β #{0}) ; { _ } }}. 
  (* TODO *)
  (* refine {{ voting_result_.set(FALSE) ; { _ } }}.  *)
  refine {{ voting_result_ -> set(FALSE) ; { _ } }}.  
  refine {{ voting_code_hash_ := (β #{0}) ; { _ } }}. 
  refine {{ voting_id_ := (β #{0}) ; { _ } }}. 
  refine {{ return_ {} }}.
Defined. 
Definition constructor_left {R b0 b1 } 
(min_summa: URValue  XUInteger128  b0 ) 
(max_summa: URValue  XUInteger128  b1 ) 
 : UExpression R (orb(orb true b1)b0) :=
wrapULExpression (ursus_call_with_args λ2 constructor_ min_summa max_summa ).
Notation " 'constructor' '(' min_summa ',' max_summa ')' " := 
(constructor_left min_summa max_summa )  
(in custom ULValue at level 0 , 
min_summa custom URValue at level 0, 
max_summa custom URValue at level 0) : ursus_scope.
End DBlankFuncs .

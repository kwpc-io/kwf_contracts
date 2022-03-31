Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import KWDPool.DKWDPool.ClassTypes.
Require Import KWDPool.DKWDPool.Interface.

Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import Interfaces.IKWFund.IKWFund.ClassTypes.
(* Require Import KWErrorConstants.KWErrors.ClassTypes.
Require Import KWMessagesConstants.KWMessages.ClassTypes. *)
Import UrsusNotations.
Local Open Scope ursus_scope.

Section ClassTypesNotationsDef.
Context {Ledger LedgerMainState LedgerLocalState  LedgerMessagesAndEvents  : Type}.
Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord}.

Notation UExpression := (@UExpressionL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass) .
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass) .
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass) .
Notation wrapULExpression := (@wrapULExpressionL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _ _ _ ).
Notation ursus_call_with_args := (@ursus_call_with_argsL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _  ).


(*определения для external/public функций*)
Definition IDKWDPool_Ф_isFundReady_right : URValue IDKWDPool false.
refine ( ( URScalar (KWDPool.DKWDPool.Interface.IisFundReady : IDKWDPool ) ) : URValue _ _ ) .
Defined.

Definition IDKWDPool_Ф_getBalance_right : URValue IDKWDPool false.
refine ( ( URScalar (KWDPool.DKWDPool.Interface.IgetBalance : IDKWDPool ) ) : URValue _ _ ) .
Defined.

Definition IDKWDPool_Ф_isInitialized_right : URValue IDKWDPool false.
refine ( ( URScalar (KWDPool.DKWDPool.Interface.IisInitialized : IDKWDPool ) ) : URValue _ _ ) .
Defined.

Definition IDKWDPool_Ф_onVoteAccept_right : URValue IDKWDPool false.
refine ( ( URScalar (KWDPool.DKWDPool.Interface.IonVoteAccept : IDKWDPool ) ) : URValue _ _ ) .
Defined.

Definition IDKWDPool_Ф_onVoteReject_right { b0 }

(voting_id : URValue ( XUInteger8 ) b0 ): URValue IDKWDPool b0.
pose proof (
urvalue_bind voting_id (fun voting_id' => URScalar ( KWDPool.DKWDPool.Interface.IonVoteReject voting_id' : IDKWDPool )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_vote_right { b0 b1 b2 }

(choice : URValue ( XBool  ) b0 )
(voting_id : URValue ( XUInteger8 ) b1 )
(code_hash : URValue ( XUInteger256 ) b2 ): URValue IDKWDPool (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind choice (fun choice' => 
urvalue_bind voting_id (fun voting_id' => 
urvalue_bind code_hash (fun code_hash' => URScalar ( KWDPool.DKWDPool.Interface.Ivote choice' voting_id' code_hash' : IDKWDPool )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_returnExtraFunds_right { b0 }

(address_to : URValue ( address  ) b0 ): URValue IDKWDPool b0.
pose proof (
urvalue_bind address_to (fun address_to' => URScalar ( KWDPool.DKWDPool.Interface.IreturnExtraFunds address_to' : IDKWDPool )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_returnFunds_right { b0 }

(address_to : URValue ( address  ) b0 ): URValue IDKWDPool b0.
pose proof (
urvalue_bind address_to (fun address_to' => URScalar ( KWDPool.DKWDPool.Interface.IreturnFunds address_to' : IDKWDPool )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_sendFunds_right { b0 }

(code : URValue ( cell_  ) b0 ): URValue IDKWDPool b0.
pose proof (
urvalue_bind code (fun code' => URScalar ( KWDPool.DKWDPool.Interface.IsendFunds code' : IDKWDPool )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_acknowledgeFunds_right : URValue IDKWDPool false.
refine ( ( URScalar (KWDPool.DKWDPool.Interface.IacknowledgeFunds : IDKWDPool ) ) : URValue _ _ ) .
Defined.

Definition IDKWDPool_Ф_setFinalAddress_right { b0 }

(final_address : URValue ( address  ) b0 ): URValue IDKWDPool b0.
pose proof (
urvalue_bind final_address (fun final_address' => URScalar ( KWDPool.DKWDPool.Interface.IsetFinalAddress final_address' : IDKWDPool )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_notifyParticipant_right { b0 b1 b2 }

(giveup : URValue ( XBool  ) b0 )
(investors_adj_summa_ : URValue ( XUInteger128 ) b1 )
(summa_givers : URValue ( XUInteger128 ) b2 ): URValue IDKWDPool (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giveup (fun giveup' => 
urvalue_bind investors_adj_summa_ (fun investors_adj_summa_' => 
urvalue_bind summa_givers (fun summa_givers' => URScalar ( KWDPool.DKWDPool.Interface.InotifyParticipant giveup' investors_adj_summa_' summa_givers' : IDKWDPool )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_receive_right : URValue IDKWDPool false.
refine ( ( URScalar (KWDPool.DKWDPool.Interface.Ireceive : IDKWDPool ) ) : URValue _ _ ) .
Defined.

Definition IDKWDPool_Ф_initialize_right { b0 b1 b2 b3 b4 }

(lock_time : URValue ( XUInteger32 ) b0 )
(unlock_time : URValue ( XUInteger32 ) b1 )
(quant : URValue ( XUInteger128 ) b2 )
(rate : URValue ( XUInteger8 ) b3 )
(kwf_lock_time : URValue ( XUInteger32 ) b4 ): URValue IDKWDPool (orb b0 (orb b1 (orb b2 (orb b3 b4)))).
pose proof (
urvalue_bind lock_time (fun lock_time' => 
urvalue_bind unlock_time (fun unlock_time' => 
urvalue_bind quant (fun quant' => 
urvalue_bind rate (fun rate' => 
urvalue_bind kwf_lock_time (fun kwf_lock_time' => URScalar ( KWDPool.DKWDPool.Interface.Iinitialize lock_time' unlock_time' quant' rate' kwf_lock_time' : IDKWDPool )
))))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDKWDPool_Ф_constructor_right { b0 }

(final_address : URValue ( XMaybe  (  address  ) ) b0 ): URValue IDKWDPool b0.
pose proof (
urvalue_bind final_address (fun final_address' => URScalar ( KWDPool.DKWDPool.Interface._Iconstructor final_address' : IDKWDPool )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'DKWDPool.isFundReady' '('  ')' " := (IDKWDPool_Ф_isFundReady_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.getBalance' '('  ')' " := (IDKWDPool_Ф_getBalance_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.isInitialized' '('  ')' " := (IDKWDPool_Ф_isInitialized_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.onVoteAccept' '('  ')' " := (IDKWDPool_Ф_onVoteAccept_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.onVoteReject' '(' voting_id ')' " := (IDKWDPool_Ф_onVoteReject_right voting_id ) (in custom URValue at level 0 ,
voting_id custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.vote' '(' choice ',' voting_id ',' code_hash ')' " := (IDKWDPool_Ф_vote_right choice voting_id code_hash ) (in custom URValue at level 0 ,
choice custom URValue at level 0  ,
voting_id custom URValue at level 0  ,
code_hash custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.returnExtraFunds' '(' address_to ')' " := (IDKWDPool_Ф_returnExtraFunds_right address_to ) (in custom URValue at level 0 ,
address_to custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.returnFunds' '(' address_to ')' " := (IDKWDPool_Ф_returnFunds_right address_to ) (in custom URValue at level 0 ,
address_to custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.sendFunds' '(' code ')' " := (IDKWDPool_Ф_sendFunds_right code ) (in custom URValue at level 0 ,
code custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.acknowledgeFunds' '('  ')' " := (IDKWDPool_Ф_acknowledgeFunds_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.setFinalAddress' '(' final_address ')' " := (IDKWDPool_Ф_setFinalAddress_right final_address ) (in custom URValue at level 0 ,
final_address custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.notifyParticipant' '(' giveup ',' investors_adj_summa_ ',' summa_givers ')' " := (IDKWDPool_Ф_notifyParticipant_right giveup investors_adj_summa_ summa_givers ) (in custom URValue at level 0 ,
giveup custom URValue at level 0  ,
investors_adj_summa_ custom URValue at level 0  ,
summa_givers custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.receive' '('  ')' " := (IDKWDPool_Ф_receive_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.initialize' '(' lock_time ',' unlock_time ',' quant ',' rate ',' kwf_lock_time ')' " := (IDKWDPool_Ф_initialize_right lock_time unlock_time quant rate kwf_lock_time ) (in custom URValue at level 0 ,
lock_time custom URValue at level 0  ,
unlock_time custom URValue at level 0  ,
quant custom URValue at level 0  ,
rate custom URValue at level 0  ,
kwf_lock_time custom URValue at level 0 ) : ursus_scope . 
Notation " 'DKWDPool.constructor' '(' final_address ')' " := (IDKWDPool_Ф_constructor_right final_address ) (in custom URValue at level 0 ,
final_address custom URValue at level 0 ) : ursus_scope . 
Notation " 'new' lm 'with' d '(' final_address ')' " := (tvm_newContract_right lm d (IDKWDPool_Ф_constructor_right final_address) )
(in custom URValue at level 0 (* , lm custom ULValue at level 0 *), d custom URValue at level 0 ) : ursus_scope .
Notation " 'new' lm 'with' d '(' final_address ')' " := (tvm_newContract_left lm d (IDKWDPool_Ф_constructor_right final_address) )
(in custom ULValue at level 0 , lm custom ULValue at level 0, d custom URValue at level 0 ) : ursus_scope .
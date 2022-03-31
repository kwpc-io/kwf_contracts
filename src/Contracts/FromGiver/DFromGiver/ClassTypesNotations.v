Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import FromGiver.DFromGiver.ClassTypes.
Require Import FromGiver.DFromGiver.Interface.

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
Definition IDFromGiver_Ф_onVoteAccept_right : URValue IDFromGiver false.
refine ( ( URScalar (FromGiver.DFromGiver.Interface.IonVoteAccept : IDFromGiver ) ) : URValue _ _ ) .
Defined.

Definition IDFromGiver_Ф_onVoteReject_right { b0 }

(voting_id : URValue ( XUInteger8 ) b0 ): URValue IDFromGiver b0.
pose proof (
urvalue_bind voting_id (fun voting_id' => URScalar ( FromGiver.DFromGiver.Interface.IonVoteReject voting_id' : IDFromGiver )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDFromGiver_Ф_returnFunds_right : URValue IDFromGiver false.
refine ( ( URScalar (FromGiver.DFromGiver.Interface.IreturnFunds : IDFromGiver ) ) : URValue _ _ ) .
Defined.

Definition IDFromGiver_Ф_sendFunds_right { b0 }

(NO_NAME0 : URValue ( cell_  ) b0 ): URValue IDFromGiver b0.
pose proof (
urvalue_bind NO_NAME0 (fun NO_NAME0' => URScalar ( FromGiver.DFromGiver.Interface.IsendFunds NO_NAME0' : IDFromGiver )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDFromGiver_Ф_acknowledgeFunds_right : URValue IDFromGiver false.
refine ( ( URScalar (FromGiver.DFromGiver.Interface.IacknowledgeFunds : IDFromGiver ) ) : URValue _ _ ) .
Defined.

Definition IDFromGiver_Ф_notifyParticipant_right { b0 b1 b2 }

(giveup : URValue ( XBool  ) b0 )
(investors_adj_summa_ : URValue ( XUInteger128 ) b1 )
(summa_givers : URValue ( XUInteger128 ) b2 ): URValue IDFromGiver (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giveup (fun giveup' => 
urvalue_bind investors_adj_summa_ (fun investors_adj_summa_' => 
urvalue_bind summa_givers (fun summa_givers' => URScalar ( FromGiver.DFromGiver.Interface.InotifyParticipant giveup' investors_adj_summa_' summa_givers' : IDFromGiver )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDFromGiver_Ф_receive_right : URValue IDFromGiver false.
refine ( ( URScalar (FromGiver.DFromGiver.Interface.Ireceive : IDFromGiver ) ) : URValue _ _ ) .
Defined.

Definition IDFromGiver_Ф_initialize_right { b0 b1 b2 b3 b4 }

(NO_NAME0 : URValue ( XUInteger32 ) b0 )
(NO_NAME1 : URValue ( XUInteger32 ) b1 )
(NO_NAME2 : URValue ( XUInteger128 ) b2 )
(NO_NAME3 : URValue ( XUInteger8 ) b3 )
(NO_NAME4 : URValue ( XUInteger32 ) b4 ): URValue IDFromGiver (orb b0 (orb b1 (orb b2 (orb b3 b4)))).
pose proof (
urvalue_bind NO_NAME0 (fun NO_NAME0' => 
urvalue_bind NO_NAME1 (fun NO_NAME1' => 
urvalue_bind NO_NAME2 (fun NO_NAME2' => 
urvalue_bind NO_NAME3 (fun NO_NAME3' => 
urvalue_bind NO_NAME4 (fun NO_NAME4' => URScalar ( FromGiver.DFromGiver.Interface.Iinitialize NO_NAME0' NO_NAME1' NO_NAME2' NO_NAME3' NO_NAME4' : IDFromGiver )
))))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDFromGiver_Ф_constructor_right { b0 b1 }

(lock_time : URValue ( XUInteger32 ) b0 )
(unlock_time : URValue ( XUInteger32 ) b1 ): URValue IDFromGiver (orb b0 b1).
pose proof (
urvalue_bind lock_time (fun lock_time' => 
urvalue_bind unlock_time (fun unlock_time' => URScalar ( FromGiver.DFromGiver.Interface._Iconstructor lock_time' unlock_time' : IDFromGiver )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'DFromGiver.onVoteAccept' '('  ')' " := (IDFromGiver_Ф_onVoteAccept_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.onVoteReject' '(' voting_id ')' " := (IDFromGiver_Ф_onVoteReject_right voting_id ) (in custom URValue at level 0 ,
voting_id custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.returnFunds' '('  ')' " := (IDFromGiver_Ф_returnFunds_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.sendFunds' '(' NO_NAME0 ')' " := (IDFromGiver_Ф_sendFunds_right NO_NAME0 ) (in custom URValue at level 0 ,
NO_NAME0 custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.acknowledgeFunds' '('  ')' " := (IDFromGiver_Ф_acknowledgeFunds_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.notifyParticipant' '(' giveup ',' investors_adj_summa_ ',' summa_givers ')' " := (IDFromGiver_Ф_notifyParticipant_right giveup investors_adj_summa_ summa_givers ) (in custom URValue at level 0 ,
giveup custom URValue at level 0  ,
investors_adj_summa_ custom URValue at level 0  ,
summa_givers custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.receive' '('  ')' " := (IDFromGiver_Ф_receive_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.initialize' '(' NO_NAME0 ',' NO_NAME1 ',' NO_NAME2 ',' NO_NAME3 ',' NO_NAME4 ')' " := (IDFromGiver_Ф_initialize_right NO_NAME0 NO_NAME1 NO_NAME2 NO_NAME3 NO_NAME4 ) (in custom URValue at level 0 ,
NO_NAME0 custom URValue at level 0  ,
NO_NAME1 custom URValue at level 0  ,
NO_NAME2 custom URValue at level 0  ,
NO_NAME3 custom URValue at level 0  ,
NO_NAME4 custom URValue at level 0 ) : ursus_scope . 
Notation " 'DFromGiver.constructor' '(' lock_time ',' unlock_time ')' " := (IDFromGiver_Ф_constructor_right lock_time unlock_time ) (in custom URValue at level 0 ,
lock_time custom URValue at level 0  ,
unlock_time custom URValue at level 0 ) : ursus_scope . 
Notation " 'new' lm 'with' d '(' lock_time , unlock_time ')' " := (tvm_newContract_right lm d (IDFromGiver_Ф_constructor_right lock_time unlock_time) )
(in custom URValue at level 0 (* , lm custom ULValue at level 0 *), d custom URValue at level 0 ) : ursus_scope .
Notation " 'new' lm 'with' d '(' lock_time , unlock_time ')' " := (tvm_newContract_left lm d (IDFromGiver_Ф_constructor_right lock_time unlock_time) )
(in custom ULValue at level 0 , lm custom ULValue at level 0, d custom URValue at level 0 ) : ursus_scope .
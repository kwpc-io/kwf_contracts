Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.


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
Definition IKWFundParticipant_Ф_onVoteReject_right { b0 }

(voting_id : URValue ( XUInteger8 ) b0 ): URValue IKWFundParticipant b0.
pose proof (
urvalue_bind voting_id (fun voting_id' => URScalar ( IKWFundParticipant.IKWFundParticipant.Interface.IonVoteReject voting_id' : IKWFundParticipant )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IKWFundParticipant_Ф_onVoteAccept_right : URValue IKWFundParticipant false.
refine ( ( URScalar (IKWFundParticipant.IKWFundParticipant.Interface.IonVoteAccept : IKWFundParticipant ) ) : URValue _ _ ) .
Defined.

Definition IKWFundParticipant_Ф_acknowledgeFunds_right : URValue IKWFundParticipant false.
refine ( ( URScalar (IKWFundParticipant.IKWFundParticipant.Interface.IacknowledgeFunds : IKWFundParticipant ) ) : URValue _ _ ) .
Defined.

Definition IKWFundParticipant_Ф_sendFunds_right { b0 }

(code : URValue ( cell_  ) b0 ): URValue IKWFundParticipant b0.
pose proof (
urvalue_bind code (fun code' => URScalar ( IKWFundParticipant.IKWFundParticipant.Interface.IsendFunds code' : IKWFundParticipant )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IKWFundParticipant_Ф_initialize_right { b0 b1 b2 b3 b4 }

(lock_time : URValue ( XUInteger32 ) b0 )
(unlock_time : URValue ( XUInteger32 ) b1 )
(quant : URValue ( XUInteger128 ) b2 )
(rate : URValue ( XUInteger8 ) b3 )
(kwf_lock_time : URValue ( XUInteger32 ) b4 ): URValue IKWFundParticipant (orb b0 (orb b1 (orb b2 (orb b3 b4)))).
pose proof (
urvalue_bind lock_time (fun lock_time' => 
urvalue_bind unlock_time (fun unlock_time' => 
urvalue_bind quant (fun quant' => 
urvalue_bind rate (fun rate' => 
urvalue_bind kwf_lock_time (fun kwf_lock_time' => URScalar ( IKWFundParticipant.IKWFundParticipant.Interface.Iinitialize lock_time' unlock_time' quant' rate' kwf_lock_time' : IKWFundParticipant )
))))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IKWFundParticipant_Ф_notifyParticipant_right { b0 b1 b2 }

(giveup : URValue ( XBool  ) b0 )
(summa_investors : URValue ( XUInteger128 ) b1 )
(summa_givers : URValue ( XUInteger128 ) b2 ): URValue IKWFundParticipant (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giveup (fun giveup' => 
urvalue_bind summa_investors (fun summa_investors' => 
urvalue_bind summa_givers (fun summa_givers' => URScalar ( IKWFundParticipant.IKWFundParticipant.Interface.InotifyParticipant giveup' summa_investors' summa_givers' : IKWFundParticipant )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'IKWFundParticipant.onVoteReject' '(' voting_id ')' " := (IKWFundParticipant_Ф_onVoteReject_right voting_id ) (in custom URValue at level 0 ,
voting_id custom URValue at level 0 ) : ursus_scope . 
Notation " 'IKWFundParticipant.onVoteAccept' '('  ')' " := (IKWFundParticipant_Ф_onVoteAccept_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'IKWFundParticipant.acknowledgeFunds' '('  ')' " := (IKWFundParticipant_Ф_acknowledgeFunds_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'IKWFundParticipant.sendFunds' '(' code ')' " := (IKWFundParticipant_Ф_sendFunds_right code ) (in custom URValue at level 0 ,
code custom URValue at level 0 ) : ursus_scope . 
Notation " 'IKWFundParticipant.initialize' '(' lock_time ',' unlock_time ',' quant ',' rate ',' kwf_lock_time ')' " := (IKWFundParticipant_Ф_initialize_right lock_time unlock_time quant rate kwf_lock_time ) (in custom URValue at level 0 ,
lock_time custom URValue at level 0  ,
unlock_time custom URValue at level 0  ,
quant custom URValue at level 0  ,
rate custom URValue at level 0  ,
kwf_lock_time custom URValue at level 0 ) : ursus_scope . 
Notation " 'IKWFundParticipant.notifyParticipant' '(' giveup ',' summa_investors ',' summa_givers ')' " := (IKWFundParticipant_Ф_notifyParticipant_right giveup summa_investors summa_givers ) (in custom URValue at level 0 ,
giveup custom URValue at level 0  ,
summa_investors custom URValue at level 0  ,
summa_givers custom URValue at level 0 ) : ursus_scope . 
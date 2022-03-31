Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import Interfaces.IKWFund.IKWFund.Interface.


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
Definition IKWFund_Ф_sendKWDPoolParams_right { b0 b1 b2 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(params : URValue ( cell_  ) b2 ): URValue IKWFund (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind params (fun params' => URScalar ( IKWFund.IKWFund.Interface.IsendKWDPoolParams pk' nonce' params' : IKWFund )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IKWFund_Ф_sendFromGiverParams_right { b0 b1 b2 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(params : URValue ( cell_  ) b2 ): URValue IKWFund (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind params (fun params' => URScalar ( IKWFund.IKWFund.Interface.IsendFromGiverParams giver' nonce' params' : IKWFund )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'IKWFund.sendKWDPoolParams' '(' pk ',' nonce ',' params ')' " := (IKWFund_Ф_sendKWDPoolParams_right pk nonce params ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0  ,
params custom URValue at level 0 ) : ursus_scope . 
Notation " 'IKWFund.sendFromGiverParams' '(' giver ',' nonce ',' params ')' " := (IKWFund_Ф_sendFromGiverParams_right giver nonce params ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0  ,
params custom URValue at level 0 ) : ursus_scope . 
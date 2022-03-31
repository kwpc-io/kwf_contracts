Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import Interfaces.IBlank.IBlank.Interface.


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
Definition IBlank_Ф_vote_right { b0 b1 b2 b3 b4 b5 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(choice : URValue ( XBool  ) b2 )
(sum : URValue ( XUInteger128 ) b3 )
(voting_id : URValue ( XUInteger8 ) b4 )
(code_hash : URValue ( XUInteger256 ) b5 ): URValue IBlank (orb b0 (orb b1 (orb b2 (orb b3 (orb b4 b5))))).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind choice (fun choice' => 
urvalue_bind sum (fun sum' => 
urvalue_bind voting_id (fun voting_id' => 
urvalue_bind code_hash (fun code_hash' => URScalar ( IBlank.IBlank.Interface.Ivote pk' nonce' choice' sum' voting_id' code_hash' : IBlank )
)))))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IBlank_Ф_acknowledgeDeploy_right { b0 b1 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 ): URValue IBlank (orb b0 b1).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => URScalar ( IBlank.IBlank.Interface.IacknowledgeDeploy giver' nonce' : IBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IBlank_Ф_acknowledgeFinalizeRight_right { b0 b1 b2 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(dead_giver : URValue ( XBool  ) b2 ): URValue IBlank (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind dead_giver (fun dead_giver' => URScalar ( IBlank.IBlank.Interface.IacknowledgeFinalizeRight giver' nonce' dead_giver' : IBlank )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IBlank_Ф_acknowledgeFinalizeLeft_right { b0 b1 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 ): URValue IBlank (orb b0 b1).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => URScalar ( IBlank.IBlank.Interface.IacknowledgeFinalizeLeft pk' nonce' : IBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IBlank_Ф_isFundReady_right { b0 b1 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 ): URValue IBlank (orb b0 b1).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => URScalar ( IBlank.IBlank.Interface.IisFundReady pk' nonce' : IBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IBlank_Ф_notifyRight_right { b0 b1 b2 b3 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(balance : URValue ( XUInteger128 ) b2 )
(income : URValue ( XUInteger128 ) b3 ): URValue IBlank (orb b0 (orb b1 (orb b2 b3))).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind balance (fun balance' => 
urvalue_bind income (fun income' => URScalar ( IBlank.IBlank.Interface.InotifyRight giver' nonce' balance' income' : IBlank )
)))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IBlank_Ф_notifyLeft_right { b0 b1 b2 b3 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(balance : URValue ( XUInteger128 ) b2 )
(adj_balance : URValue ( XUInteger128 ) b3 ): URValue IBlank (orb b0 (orb b1 (orb b2 b3))).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind balance (fun balance' => 
urvalue_bind adj_balance (fun adj_balance' => URScalar ( IBlank.IBlank.Interface.InotifyLeft pk' nonce' balance' adj_balance' : IBlank )
)))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'IBlank.vote' '(' pk ',' nonce ',' choice ',' sum ',' voting_id ',' code_hash ')' " := (IBlank_Ф_vote_right pk nonce choice sum voting_id code_hash ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0  ,
choice custom URValue at level 0  ,
sum custom URValue at level 0  ,
voting_id custom URValue at level 0  ,
code_hash custom URValue at level 0 ) : ursus_scope . 
Notation " 'IBlank.acknowledgeDeploy' '(' giver ',' nonce ')' " := (IBlank_Ф_acknowledgeDeploy_right giver nonce ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'IBlank.acknowledgeFinalizeRight' '(' giver ',' nonce ',' dead_giver ')' " := (IBlank_Ф_acknowledgeFinalizeRight_right giver nonce dead_giver ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0  ,
dead_giver custom URValue at level 0 ) : ursus_scope . 
Notation " 'IBlank.acknowledgeFinalizeLeft' '(' pk ',' nonce ')' " := (IBlank_Ф_acknowledgeFinalizeLeft_right pk nonce ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'IBlank.isFundReady' '(' pk ',' nonce ')' " := (IBlank_Ф_isFundReady_right pk nonce ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'IBlank.notifyRight' '(' giver ',' nonce ',' balance ',' income ')' " := (IBlank_Ф_notifyRight_right giver nonce balance income ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0  ,
balance custom URValue at level 0  ,
income custom URValue at level 0 ) : ursus_scope . 
Notation " 'IBlank.notifyLeft' '(' pk ',' nonce ',' balance ',' adj_balance ')' " := (IBlank_Ф_notifyLeft_right pk nonce balance adj_balance ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0  ,
balance custom URValue at level 0  ,
adj_balance custom URValue at level 0 ) : ursus_scope . 
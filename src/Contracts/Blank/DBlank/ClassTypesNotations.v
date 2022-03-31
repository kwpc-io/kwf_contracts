Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Blank.DBlank.ClassTypes.
Require Import Blank.DBlank.Interface.

Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import KWDPool.DKWDPool.ClassTypes.
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
Definition IDBlank_Ф_getTimes_right : URValue IDBlank false.
refine ( ( URScalar (Blank.DBlank.Interface.IgetTimes : IDBlank ) ) : URValue _ _ ) .
Defined.

Definition IDBlank_Ф_getInvestorsNumbers_right : URValue IDBlank false.
refine ( ( URScalar (Blank.DBlank.Interface.IgetInvestorsNumbers : IDBlank ) ) : URValue _ _ ) .
Defined.

Definition IDBlank_Ф_getGiversSum_right : URValue IDBlank false.
refine ( ( URScalar (Blank.DBlank.Interface.IgetGiversSum : IDBlank ) ) : URValue _ _ ) .
Defined.

Definition IDBlank_Ф_getInvestorsSum_right : URValue IDBlank false.
refine ( ( URScalar (Blank.DBlank.Interface.IgetInvestorsSum : IDBlank ) ) : URValue _ _ ) .
Defined.

Definition IDBlank_Ф_killBlank_right { b0 }

(address_to : URValue ( address  ) b0 ): URValue IDBlank b0.
pose proof (
urvalue_bind address_to (fun address_to' => URScalar ( Blank.DBlank.Interface.IkillBlank address_to' : IDBlank )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_startVoting_right { b0 b1 }

(voting_time : URValue ( XUInteger32 ) b0 )
(code_hash : URValue ( XUInteger256 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind voting_time (fun voting_time' => 
urvalue_bind code_hash (fun code_hash' => URScalar ( Blank.DBlank.Interface.IstartVoting voting_time' code_hash' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_vote_right { b0 b1 b2 b3 b4 b5 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(choice : URValue ( XBool  ) b2 )
(sum : URValue ( XUInteger128 ) b3 )
(voting_id : URValue ( XUInteger8 ) b4 )
(code_hash : URValue ( XUInteger256 ) b5 ): URValue IDBlank (orb b0 (orb b1 (orb b2 (orb b3 (orb b4 b5))))).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind choice (fun choice' => 
urvalue_bind sum (fun sum' => 
urvalue_bind voting_id (fun voting_id' => 
urvalue_bind code_hash (fun code_hash' => URScalar ( Blank.DBlank.Interface.Ivote pk' nonce' choice' sum' voting_id' code_hash' : IDBlank )
)))))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_setFundCode_right { b0 }

(code : URValue ( cell_  ) b0 ): URValue IDBlank b0.
pose proof (
urvalue_bind code (fun code' => URScalar ( Blank.DBlank.Interface.IsetFundCode code' : IDBlank )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_finalize_right { b0 b1 }

(force_giveup : URValue ( XBool  ) b0 )
(addr : URValue ( address  ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind force_giveup (fun force_giveup' => 
urvalue_bind addr (fun addr' => URScalar ( Blank.DBlank.Interface.Ifinalize force_giveup' addr' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_acknowledgeFinalizeRight_right { b0 b1 b2 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(dead_giver : URValue ( XBool  ) b2 ): URValue IDBlank (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind dead_giver (fun dead_giver' => URScalar ( Blank.DBlank.Interface.IacknowledgeFinalizeRight giver' nonce' dead_giver' : IDBlank )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_acknowledgeFinalizeLeft_right { b0 b1 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => URScalar ( Blank.DBlank.Interface.IacknowledgeFinalizeLeft pk' nonce' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_notifyRight_right { b0 b1 b2 b3 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(balance : URValue ( XUInteger128 ) b2 )
(income : URValue ( XUInteger128 ) b3 ): URValue IDBlank (orb b0 (orb b1 (orb b2 b3))).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind balance (fun balance' => 
urvalue_bind income (fun income' => URScalar ( Blank.DBlank.Interface.InotifyRight giver' nonce' balance' income' : IDBlank )
)))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_acknowledgeDeploy_right { b0 b1 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => URScalar ( Blank.DBlank.Interface.IacknowledgeDeploy giver' nonce' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_deployFromGiver_right { b0 b1 b2 }

(code : URValue ( cell_  ) b0 )
(giver : URValue ( address  ) b1 )
(nonce : URValue ( XUInteger256 ) b2 ): URValue IDBlank (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind code (fun code' => 
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => URScalar ( Blank.DBlank.Interface.IdeployFromGiver code' giver' nonce' : IDBlank )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_notifyLeft_right { b0 b1 b2 b3 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(balance : URValue ( XUInteger128 ) b2 )
(adj_balance : URValue ( XUInteger128 ) b3 ): URValue IDBlank (orb b0 (orb b1 (orb b2 b3))).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind balance (fun balance' => 
urvalue_bind adj_balance (fun adj_balance' => URScalar ( Blank.DBlank.Interface.InotifyLeft pk' nonce' balance' adj_balance' : IDBlank )
)))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_isFundReady_right { b0 b1 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => URScalar ( Blank.DBlank.Interface.IisFundReady pk' nonce' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_setKWDPoolCodeHash_right { b0 b1 }

(code_hash : URValue ( XUInteger256 ) b0 )
(code_depth : URValue ( XUInteger16 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind code_hash (fun code_hash' => 
urvalue_bind code_depth (fun code_depth' => URScalar ( Blank.DBlank.Interface.IsetKWDPoolCodeHash code_hash' code_depth' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_setFromGiverCodeHash_right { b0 b1 }

(code_hash : URValue ( XUInteger256 ) b0 )
(code_depth : URValue ( XUInteger16 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind code_hash (fun code_hash' => 
urvalue_bind code_depth (fun code_depth' => URScalar ( Blank.DBlank.Interface.IsetFromGiverCodeHash code_hash' code_depth' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDBlank_Ф_constructor_right { b0 b1 }

(min_summa : URValue ( XUInteger128 ) b0 )
(max_summa : URValue ( XUInteger128 ) b1 ): URValue IDBlank (orb b0 b1).
pose proof (
urvalue_bind min_summa (fun min_summa' => 
urvalue_bind max_summa (fun max_summa' => URScalar ( Blank.DBlank.Interface._Iconstructor min_summa' max_summa' : IDBlank )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'DBlank.getTimes' '('  ')' " := (IDBlank_Ф_getTimes_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.getInvestorsNumbers' '('  ')' " := (IDBlank_Ф_getInvestorsNumbers_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.getGiversSum' '('  ')' " := (IDBlank_Ф_getGiversSum_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.getInvestorsSum' '('  ')' " := (IDBlank_Ф_getInvestorsSum_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.killBlank' '(' address_to ')' " := (IDBlank_Ф_killBlank_right address_to ) (in custom URValue at level 0 ,
address_to custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.startVoting' '(' voting_time ',' code_hash ')' " := (IDBlank_Ф_startVoting_right voting_time code_hash ) (in custom URValue at level 0 ,
voting_time custom URValue at level 0  ,
code_hash custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.vote' '(' pk ',' nonce ',' choice ',' sum ',' voting_id ',' code_hash ')' " := (IDBlank_Ф_vote_right pk nonce choice sum voting_id code_hash ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0  ,
choice custom URValue at level 0  ,
sum custom URValue at level 0  ,
voting_id custom URValue at level 0  ,
code_hash custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.setFundCode' '(' code ')' " := (IDBlank_Ф_setFundCode_right code ) (in custom URValue at level 0 ,
code custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.finalize' '(' force_giveup ',' addr ')' " := (IDBlank_Ф_finalize_right force_giveup addr ) (in custom URValue at level 0 ,
force_giveup custom URValue at level 0  ,
addr custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.acknowledgeFinalizeRight' '(' giver ',' nonce ',' dead_giver ')' " := (IDBlank_Ф_acknowledgeFinalizeRight_right giver nonce dead_giver ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0  ,
dead_giver custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.acknowledgeFinalizeLeft' '(' pk ',' nonce ')' " := (IDBlank_Ф_acknowledgeFinalizeLeft_right pk nonce ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.notifyRight' '(' giver ',' nonce ',' balance ',' income ')' " := (IDBlank_Ф_notifyRight_right giver nonce balance income ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0  ,
balance custom URValue at level 0  ,
income custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.acknowledgeDeploy' '(' giver ',' nonce ')' " := (IDBlank_Ф_acknowledgeDeploy_right giver nonce ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.deployFromGiver' '(' code ',' giver ',' nonce ')' " := (IDBlank_Ф_deployFromGiver_right code giver nonce ) (in custom URValue at level 0 ,
code custom URValue at level 0  ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.notifyLeft' '(' pk ',' nonce ',' balance ',' adj_balance ')' " := (IDBlank_Ф_notifyLeft_right pk nonce balance adj_balance ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0  ,
balance custom URValue at level 0  ,
adj_balance custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.isFundReady' '(' pk ',' nonce ')' " := (IDBlank_Ф_isFundReady_right pk nonce ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.setKWDPoolCodeHash' '(' code_hash ',' code_depth ')' " := (IDBlank_Ф_setKWDPoolCodeHash_right code_hash code_depth ) (in custom URValue at level 0 ,
code_hash custom URValue at level 0  ,
code_depth custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.setFromGiverCodeHash' '(' code_hash ',' code_depth ')' " := (IDBlank_Ф_setFromGiverCodeHash_right code_hash code_depth ) (in custom URValue at level 0 ,
code_hash custom URValue at level 0  ,
code_depth custom URValue at level 0 ) : ursus_scope . 
Notation " 'DBlank.constructor' '(' min_summa ',' max_summa ')' " := (IDBlank_Ф_constructor_right min_summa max_summa ) (in custom URValue at level 0 ,
min_summa custom URValue at level 0  ,
max_summa custom URValue at level 0 ) : ursus_scope . 
Notation " 'new' lm 'with' d '(' min_summa , max_summa ')' " := (tvm_newContract_right lm d (IDBlank_Ф_constructor_right min_summa max_summa) )
(in custom URValue at level 0 (* , lm custom ULValue at level 0 *), d custom URValue at level 0 ) : ursus_scope .
Notation " 'new' lm 'with' d '(' min_summa , max_summa ')' " := (tvm_newContract_left lm d (IDBlank_Ф_constructor_right min_summa max_summa) )
(in custom ULValue at level 0 , lm custom ULValue at level 0, d custom URValue at level 0 ) : ursus_scope .
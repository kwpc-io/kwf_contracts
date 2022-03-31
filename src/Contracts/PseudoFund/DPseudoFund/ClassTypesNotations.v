Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import PseudoFund.DPseudoFund.ClassTypes.
Require Import PseudoFund.DPseudoFund.Interface.

Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import Interfaces.IKWFund.IKWFund.ClassTypes.
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
Definition IDPseudoFund_Ф_sendKWDPoolParams_right { b0 b1 b2 }

(pk : URValue ( XUInteger256 ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(NO_NAME2 : URValue ( cell_  ) b2 ): URValue IDPseudoFund (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind pk (fun pk' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind NO_NAME2 (fun NO_NAME2' => URScalar ( PseudoFund.DPseudoFund.Interface.IsendKWDPoolParams pk' nonce' NO_NAME2' : IDPseudoFund )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDPseudoFund_Ф_sendFromGiverParams_right { b0 b1 b2 }

(giver : URValue ( address  ) b0 )
(nonce : URValue ( XUInteger256 ) b1 )
(NO_NAME2 : URValue ( cell_  ) b2 ): URValue IDPseudoFund (orb b0 (orb b1 b2)).
pose proof (
urvalue_bind giver (fun giver' => 
urvalue_bind nonce (fun nonce' => 
urvalue_bind NO_NAME2 (fun NO_NAME2' => URScalar ( PseudoFund.DPseudoFund.Interface.IsendFromGiverParams giver' nonce' NO_NAME2' : IDPseudoFund )
))): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDPseudoFund_Ф_killFund_right { b0 }

(address_to : URValue ( address  ) b0 ): URValue IDPseudoFund b0.
pose proof (
urvalue_bind address_to (fun address_to' => URScalar ( PseudoFund.DPseudoFund.Interface.IkillFund address_to' : IDPseudoFund )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDPseudoFund_Ф_transferFundsTo_right { b0 b1 }

(kwdp_address : URValue ( address  ) b0 )
(code : URValue ( cell_  ) b1 ): URValue IDPseudoFund (orb b0 b1).
pose proof (
urvalue_bind kwdp_address (fun kwdp_address' => 
urvalue_bind code (fun code' => URScalar ( PseudoFund.DPseudoFund.Interface.ItransferFundsTo kwdp_address' code' : IDPseudoFund )
)): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDPseudoFund_Ф_getFromGiverFunds_right { b0 }

(from_giver_address : URValue ( address  ) b0 ): URValue IDPseudoFund b0.
pose proof (
urvalue_bind from_giver_address (fun from_giver_address' => URScalar ( PseudoFund.DPseudoFund.Interface.IgetFromGiverFunds from_giver_address' : IDPseudoFund )
): URValue _ _ ).
rewrite right_or_false in X.
refine X.
Defined.

Definition IDPseudoFund_Ф_constructor_right : URValue IDPseudoFund false.
refine ( ( URScalar (PseudoFund.DPseudoFund.Interface._Iconstructor : IDPseudoFund ) ) : URValue _ _ ) .
Defined.
End ClassTypesNotationsDef.
(* нотации для доступа извне public/external функций *)
Notation " 'DPseudoFund.sendKWDPoolParams' '(' pk ',' nonce ',' NO_NAME2 ')' " := (IDPseudoFund_Ф_sendKWDPoolParams_right pk nonce NO_NAME2 ) (in custom URValue at level 0 ,
pk custom URValue at level 0  ,
nonce custom URValue at level 0  ,
NO_NAME2 custom URValue at level 0 ) : ursus_scope . 
Notation " 'DPseudoFund.sendFromGiverParams' '(' giver ',' nonce ',' NO_NAME2 ')' " := (IDPseudoFund_Ф_sendFromGiverParams_right giver nonce NO_NAME2 ) (in custom URValue at level 0 ,
giver custom URValue at level 0  ,
nonce custom URValue at level 0  ,
NO_NAME2 custom URValue at level 0 ) : ursus_scope . 
Notation " 'DPseudoFund.killFund' '(' address_to ')' " := (IDPseudoFund_Ф_killFund_right address_to ) (in custom URValue at level 0 ,
address_to custom URValue at level 0 ) : ursus_scope . 
Notation " 'DPseudoFund.transferFundsTo' '(' kwdp_address ',' code ')' " := (IDPseudoFund_Ф_transferFundsTo_right kwdp_address code ) (in custom URValue at level 0 ,
kwdp_address custom URValue at level 0  ,
code custom URValue at level 0 ) : ursus_scope . 
Notation " 'DPseudoFund.getFromGiverFunds' '(' from_giver_address ')' " := (IDPseudoFund_Ф_getFromGiverFunds_right from_giver_address ) (in custom URValue at level 0 ,
from_giver_address custom URValue at level 0 ) : ursus_scope . 
Notation " 'DPseudoFund.constructor' '('  ')' " := (IDPseudoFund_Ф_constructor_right  ) (in custom URValue at level 0 ) : ursus_scope . 
Notation " 'new' lm 'with' d '('  ')' " := (tvm_newContract_right lm d (IDPseudoFund_Ф_constructor_right ) )
(in custom URValue at level 0 (* , lm custom ULValue at level 0 *), d custom URValue at level 0 ) : ursus_scope .
Notation " 'new' lm 'with' d '('  ')' " := (tvm_newContract_left lm d (IDPseudoFund_Ф_constructor_right ) )
(in custom ULValue at level 0 , lm custom ULValue at level 0, d custom URValue at level 0 ) : ursus_scope .
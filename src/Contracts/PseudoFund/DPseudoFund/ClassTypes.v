
Require Import FinProof.ProgrammingWith. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.

Require Import Project.CommonTypes.


Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypesNotations.

Require Import Contracts.FromGiver.DFromGiver.Interface.
Require Import Contracts.FromGiver.DFromGiver.ClassTypes.
Require Import Contracts.FromGiver.DFromGiver.ClassTypesNotations.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypesNotations.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypesNotations.

Require Import Contracts.KWDPool.DKWDPool.Interface.
Require Import Contracts.KWDPool.DKWDPool.ClassTypes.
Require Import Contracts.KWDPool.DKWDPool.ClassTypesNotations.

(* Require Import Contracts.KWErrorConstants.KWErrors.Interface.
Require Import Contracts.KWErrorConstants.KWErrors.ClassTypes.
Require Import Contracts.KWErrorConstants.KWErrors.ClassTypesNotations.

Require Import Contracts.KWMessagesConstants.KWMessages.Interface.
Require Import Contracts.KWMessagesConstants.KWMessages.ClassTypes.
Require Import Contracts.KWMessagesConstants.KWMessages.ClassTypesNotations. *)
(*Поля контракта*)

Inductive DPseudoFundFields :=
| DPseudoFund_ι_kwdpool_code_hash__ (*uint256*)
| DPseudoFund_ι_kwdpool_code_depth__ (*uint16*)
| DPseudoFund_ι_fromgiver_code_hash__ (*uint256*)
| DPseudoFund_ι_fromgiver_code_depth__ (*uint16*)
| DPseudoFund_ι_givers_summa__ (*uint128*)
| DPseudoFund_ι_investors_adj_summa__ (*uint128*)
| DPseudoFund_ι_investors_summa__ (*uint128*)
| DPseudoFund_ι_min_summa__ (*uint128*)
| DPseudoFund_ι_max_summa__ (*uint128*)
| DPseudoFund_ι_lock_time__ (*uint32*)
| DPseudoFund_ι_unlock_time__ (*uint32*)
| DPseudoFund_ι_farm_rate__ (*uint8*)
| DPseudoFund_ι_kwf_lock_time__ (*uint32*)
| DPseudoFund_ι_quant__ (*uint128*)
| DPseudoFund_ι_nonce__ (*uint256*)
| DPseudoFund_ι_num_investors_sent__ (*uint32*)
| DPseudoFund_ι_num_investors_received__ (*uint32*)
| DPseudoFund_ι_can_change_kwdpool_code__ (*bool*)
| DPseudoFund_ι_can_change_fromgiver_code__ (*bool*)
| DPseudoFund_ι_num_from_givers__ (*uint32*)
| DPseudoFund_ι_voted_for__ (*uint128*)
| DPseudoFund_ι_voted_against__ (*uint128*)
| DPseudoFund_ι_voting_start_time__ (*uint32*)
| DPseudoFund_ι_voting_time__ (*uint32*)
| DPseudoFund_ι_voting_result__ (*optional(bool)*)
| DPseudoFund_ι_voting_code_hash__ (*uint256*)
| DPseudoFund_ι_voting_id__ (*uint32*)
| DPseudoFund_ι_code_updated_ (*bool*).
Inductive VarInitFields :=
| VarInit_ι_botch0 
| VarInit_ι_botch1 .
Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Opaque address.
Definition DPseudoFundL : list Type := [ XUInteger256  : Type;
 XUInteger16  : Type;
 XUInteger256  : Type;
 XUInteger16  : Type;
 XUInteger128  : Type;
 XUInteger128  : Type;
 XUInteger128  : Type;
 XUInteger128  : Type;
 XUInteger128  : Type;
 XUInteger32  : Type;
 XUInteger32  : Type;
 XUInteger8  : Type;
 XUInteger32  : Type;
 XUInteger128  : Type;
 XUInteger256  : Type;
 XUInteger32  : Type;
 XUInteger32  : Type;
 XBool   : Type;
 XBool   : Type;
 XUInteger32  : Type;
 XUInteger128  : Type;
 XUInteger128  : Type;
 XUInteger32  : Type;
 XUInteger32  : Type;
 XMaybe  (  XBool  )  : Type;
 XUInteger256  : Type;
 XUInteger32  : Type;
 XBool   : Type].
GeneratePruvendoRecord DPseudoFundL DPseudoFundFields.
Opaque DPseudoFundLRecord.
Definition VarInitL: list Type := [
(address : Type);

(address : Type) ].
GeneratePruvendoRecord VarInitL VarInitFields.
Opaque VarInitLRecord.
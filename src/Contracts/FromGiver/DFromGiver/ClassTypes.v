
Require Import FinProof.ProgrammingWith. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.

Require Import Project.CommonTypes.


Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypesNotations.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypesNotations.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypesNotations.

(* Require Import Contracts.KWErrorConstants.KWErrors.Interface.
Require Import Contracts.KWErrorConstants.KWErrors.ClassTypes.
Require Import Contracts.KWErrorConstants.KWErrors.ClassTypesNotations.

Require Import Contracts.KWMessagesConstants.KWMessages.Interface.
Require Import Contracts.KWMessagesConstants.KWMessages.ClassTypes.
Require Import Contracts.KWMessagesConstants.KWMessages.ClassTypesNotations. *)
(*Поля контракта*)

Inductive DFromGiverFields :=
| DFromGiver_ι_balance__ (*uint128*)
| DFromGiver_ι_fund_address__ (*address*)
| DFromGiver_ι_lock_time__ (*uint32*)
| DFromGiver_ι_unlock_time__ (*uint32*)
| DFromGiver_ι_giver_address__ (*address*)
| DFromGiver_ι_fund_ready_flag__ (*bool*)
| DFromGiver_ι_nonce__ (*uint256*).
Inductive VarInitFields :=
| VarInit_ι_fund_address_ (*address*)
| VarInit_ι_giver_address_ (*address*)
| VarInit_ι_nonce_ (*uint256*).
Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Opaque address.
Definition DFromGiverL : list Type := [ XUInteger128  : Type;
 address   : Type;
 XUInteger32  : Type;
 XUInteger32  : Type;
 address   : Type;
 XBool   : Type;
 XUInteger256  : Type].
GeneratePruvendoRecord DFromGiverL DFromGiverFields.
Opaque DFromGiverLRecord.
Definition VarInitL: list Type := [ address   : Type;
 address   : Type;
 XUInteger256  : Type ].
GeneratePruvendoRecord VarInitL VarInitFields.
Opaque VarInitLRecord.
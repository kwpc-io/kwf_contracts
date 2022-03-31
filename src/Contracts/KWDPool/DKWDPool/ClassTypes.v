
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

Inductive DKWDPoolFields :=
| DKWDPool_ι_balance__ (*uint128*)
| DKWDPool_ι_fund_address__ (*address*)
| DKWDPool_ι_lock_time__ (*uint32*)
| DKWDPool_ι_unlock_time__ (*uint32*)
| DKWDPool_ι_nonce__ (*uint256*)
| DKWDPool_ι_final_address__ (*optional(address)*)
| DKWDPool_ι_quant__ (*uint128*)
| DKWDPool_ι_voting_flag__ (*bool*)
| DKWDPool_ι_fund_ready_flag__ (*bool*)
| DKWDPool_ι_init_time__ (*uint32*)
| DKWDPool_ι_deposit_time__ (*uint32*)
| DKWDPool_ι_farm_rate__ (*uint8*)
| DKWDPool_ι_kwf_lock_time__ (*uint32*)
| DKWDPool_ι_initialized__ (*bool*)
| DKWDPool_ι_voting_bitmap__ (*uint256*).
Inductive VarInitFields :=
| VarInit_ι_fund_address_ (*address*)
| VarInit_ι_nonce_ (*uint256*).
Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Opaque address.
Definition DKWDPoolL : list Type := [ XUInteger128  : Type;
 address   : Type;
 XUInteger32  : Type;
 XUInteger32  : Type;
 XUInteger256  : Type;
 XMaybe  (  address  )  : Type;
 XUInteger128  : Type;
 XBool   : Type;
 XBool   : Type;
 XUInteger32  : Type;
 XUInteger32  : Type;
 XUInteger8  : Type;
 XUInteger32  : Type;
 XBool   : Type;
 XUInteger256  : Type].
GeneratePruvendoRecord DKWDPoolL DKWDPoolFields.
Opaque DKWDPoolLRecord.
Definition VarInitL: list Type := [ address   : Type;
 XUInteger256  : Type ].
GeneratePruvendoRecord VarInitL VarInitFields.
Opaque VarInitLRecord.
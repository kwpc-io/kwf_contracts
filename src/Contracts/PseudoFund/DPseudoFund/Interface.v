
Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import PseudoFund.DPseudoFund.ClassTypes.
Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import KWDPool.DKWDPool.ClassTypes.
(* Require Import KWErrorConstants.KWErrors.ClassTypes.
Require Import KWMessagesConstants.KWMessages.ClassTypes. *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IDPseudoFund :=
| IsendKWDPoolParams : ( XUInteger256 ) -> ( XUInteger256 ) -> ( cell_  ) -> IDPseudoFund (*external*)
| IsendFromGiverParams : ( address  ) -> ( XUInteger256 ) -> ( cell_  ) -> IDPseudoFund (*external*)
| IkillFund : ( address  ) -> IDPseudoFund (*external*)
| ItransferFundsTo : ( address  ) -> ( cell_  ) -> IDPseudoFund (*external*)
| IgetFromGiverFunds : ( address  ) -> IDPseudoFund (*external*)
| _Iconstructor :   IDPseudoFund (*public*)
.

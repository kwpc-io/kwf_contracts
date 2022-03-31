
Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import Interfaces.IKWFund.IKWFund.ClassTypes.
(* Require Import KWErrorConstants.KWErrors.ClassTypes.
Require Import KWMessagesConstants.KWMessages.ClassTypes. *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IDFromGiver :=
| IonVoteAccept :   IDFromGiver (*external*)
| IonVoteReject : ( XUInteger8 ) -> IDFromGiver (*external*)
| IreturnFunds :   IDFromGiver (*external*)
| IsendFunds : ( cell_  ) -> IDFromGiver (*external*)
| IacknowledgeFunds :   IDFromGiver (*external*)
| InotifyParticipant : ( XBool  ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IDFromGiver (*external*)
| Ireceive :   IDFromGiver (*external*)
| Iinitialize : ( XUInteger32 ) -> ( XUInteger32 ) -> ( XUInteger128 ) -> ( XUInteger8 ) -> ( XUInteger32 ) -> IDFromGiver (*external*)
| _Iconstructor : ( XUInteger32 ) -> ( XUInteger32 ) -> IDFromGiver (*public*)
.


Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IKWFundParticipant :=
| IonVoteReject : ( XUInteger8 ) -> IKWFundParticipant (*external*)
| IonVoteAccept :   IKWFundParticipant (*external*)
| IacknowledgeFunds :   IKWFundParticipant (*external*)
| IsendFunds : ( cell_  ) -> IKWFundParticipant (*external*)
| Iinitialize : ( XUInteger32 ) -> ( XUInteger32 ) -> ( XUInteger128 ) -> ( XUInteger8 ) -> ( XUInteger32 ) -> IKWFundParticipant (*external*)
| InotifyParticipant : ( XBool  ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IKWFundParticipant (*external*)
.


Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import KWDPool.DKWDPool.ClassTypes.
Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import Interfaces.IKWFund.IKWFund.ClassTypes.
(* Require Import KWErrorConstants.KWErrors.ClassTypes.
Require Import KWMessagesConstants.KWMessages.ClassTypes. *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IDKWDPool :=
| IisFundReady :   IDKWDPool (*public*)
| IgetBalance :   IDKWDPool (*public*)
| IisInitialized :   IDKWDPool (*public*)
| IonVoteAccept :   IDKWDPool (*external*)
| IonVoteReject : ( XUInteger8 ) -> IDKWDPool (*external*)
| Ivote : ( XBool  ) -> ( XUInteger8 ) -> ( XUInteger256 ) -> IDKWDPool (*external*)
| IreturnExtraFunds : ( address  ) -> IDKWDPool (*external*)
| IreturnFunds : ( address  ) -> IDKWDPool (*external*)
| IsendFunds : ( cell_  ) -> IDKWDPool (*external*)
| IacknowledgeFunds :   IDKWDPool (*external*)
| IsetFinalAddress : ( address  ) -> IDKWDPool (*external*)
| InotifyParticipant : ( XBool  ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IDKWDPool (*external*)
| Ireceive :   IDKWDPool (*external*)
| Iinitialize : ( XUInteger32 ) -> ( XUInteger32 ) -> ( XUInteger128 ) -> ( XUInteger8 ) -> ( XUInteger32 ) -> IDKWDPool (*external*)
| _Iconstructor : ( XMaybe  (  address  ) ) -> IDKWDPool (*public*)
.

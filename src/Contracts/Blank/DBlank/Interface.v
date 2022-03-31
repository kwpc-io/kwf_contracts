
Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import Blank.DBlank.ClassTypes.
Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Interfaces.IBlank.IBlank.ClassTypes.
Require Import KWDPool.DKWDPool.ClassTypes.
(* Require Import KWErrorConstants.KWErrors.ClassTypes.
Require Import KWMessagesConstants.KWMessages.ClassTypes. *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IDBlank :=
| IgetTimes :   IDBlank (*public*)
| IgetInvestorsNumbers :   IDBlank (*public*)
| IgetGiversSum :   IDBlank (*public*)
| IgetInvestorsSum :   IDBlank (*public*)
| IkillBlank : ( address  ) -> IDBlank (*external*)
| IstartVoting : ( XUInteger32 ) -> ( XUInteger256 ) -> IDBlank (*external*)
| Ivote : ( XUInteger256 ) -> ( XUInteger256 ) -> ( XBool  ) -> ( XUInteger128 ) -> ( XUInteger8 ) -> ( XUInteger256 ) -> IDBlank (*external*)
| IsetFundCode : ( cell_  ) -> IDBlank (*external*)
| Ifinalize : ( XBool  ) -> ( address  ) -> IDBlank (*external*)
| IacknowledgeFinalizeRight : ( address  ) -> ( XUInteger256 ) -> ( XBool  ) -> IDBlank (*external*)
| IacknowledgeFinalizeLeft : ( XUInteger256 ) -> ( XUInteger256 ) -> IDBlank (*external*)
| InotifyRight : ( address  ) -> ( XUInteger256 ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IDBlank (*external*)
| IacknowledgeDeploy : ( address  ) -> ( XUInteger256 ) -> IDBlank (*external*)
| IdeployFromGiver : ( cell_  ) -> ( address  ) -> ( XUInteger256 ) -> IDBlank (*external*)
| InotifyLeft : ( XUInteger256 ) -> ( XUInteger256 ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IDBlank (*external*)
| IisFundReady : ( XUInteger256 ) -> ( XUInteger256 ) -> IDBlank (*external*)
| IsetKWDPoolCodeHash : ( XUInteger256 ) -> ( XUInteger16 ) -> IDBlank (*external*)
| IsetFromGiverCodeHash : ( XUInteger256 ) -> ( XUInteger16 ) -> IDBlank (*external*)
| _Iconstructor : ( XUInteger128 ) -> ( XUInteger128 ) -> IDBlank (*public*)
.


Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import Interfaces.IBlank.IBlank.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IBlank :=
| Ivote : ( XUInteger256 ) -> ( XUInteger256 ) -> ( XBool  ) -> ( XUInteger128 ) -> ( XUInteger8 ) -> ( XUInteger256 ) -> IBlank (*external*)
| IacknowledgeDeploy : ( address  ) -> ( XUInteger256 ) -> IBlank (*external*)
| IacknowledgeFinalizeRight : ( address  ) -> ( XUInteger256 ) -> ( XBool  ) -> IBlank (*external*)
| IacknowledgeFinalizeLeft : ( XUInteger256 ) -> ( XUInteger256 ) -> IBlank (*external*)
| IisFundReady : ( XUInteger256 ) -> ( XUInteger256 ) -> IBlank (*external*)
| InotifyRight : ( address  ) -> ( XUInteger256 ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IBlank (*external*)
| InotifyLeft : ( XUInteger256 ) -> ( XUInteger256 ) -> ( XUInteger128 ) -> ( XUInteger128 ) -> IBlank (*external*)
.

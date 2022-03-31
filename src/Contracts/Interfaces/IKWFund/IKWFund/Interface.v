
Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import Interfaces.IKWFund.IKWFund.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 


Inductive IKWFund :=
| IsendKWDPoolParams : ( XUInteger256 ) -> ( XUInteger256 ) -> ( cell_  ) -> IKWFund (*external*)
| IsendFromGiverParams : ( address  ) -> ( XUInteger256 ) -> ( cell_  ) -> IKWFund (*external*)
.


Require Import FinProof.ProgrammingWith. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.

Require Import Project.CommonTypes.


(*Поля контракта*)

Inductive IBlankFields :=
| IBlank_ι_botch0 
| IBlank_ι_botch1 .
Inductive VarInitFields :=
| VarInit_ι_botch0 
| VarInit_ι_botch1 .
Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Opaque address.
Definition IBlankL : list Type := [
address : Type;

address : Type].
GeneratePruvendoRecord IBlankL IBlankFields.
Opaque IBlankLRecord.
Definition VarInitL: list Type := [
(address : Type);

(address : Type) ].
GeneratePruvendoRecord VarInitL VarInitFields.
Opaque VarInitLRecord.
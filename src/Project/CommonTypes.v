Require Import FinProof.Common.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmCells.


(* 2 *)
Inductive TickTockFields := | TickTock_ι_tick  | TickTock_ι_tock  .

Local Open Scope glist_scope.

(* 2 *)Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
   ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 
Notation ErrorType := ( ErrorType XUInteger ).

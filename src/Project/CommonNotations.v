
Require Import Strings.String.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.

Require Import Project.CommonTypes.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope string_scope.

Check UExpressionL .


Notation UE := (UExpressionL _ _ _ _ _ _ _ _ _ _ ) (only parsing).
Notation UEf := (UExpressionL _ _ _ _ _ _ _ _ _ false) (only parsing).
Notation UEt := (UExpressionL _ _ _ _ _ _ _ _ _ true) (only parsing).

Notation " 'public' x " := ( x ) (at level 12, left associativity, only parsing) : ursus_scope .
Notation " 'private' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .

Tactic Notation "vararg" ident(x) constr(ss) := 
let s := fresh x in 
let T := type of x in 
refine {{new 'x : T @ ss := {} ; {_} }} ;
refine {{ {x} := #{s} ; {_} }} ;
clear s.

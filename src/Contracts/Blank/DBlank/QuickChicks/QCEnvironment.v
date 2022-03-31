Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmCells.

Require Import Project.CommonQCEnvironment.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Blank.DBlank.Ledger.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".


Local Open  Scope N_scope.

Definition LedgerDefault : LedgerLRecord  := Eval compute in default. 

#[local]
Remove Hints isoid : typeclass_instances. 
#[local]
Remove Hints iso_show : typeclass_instances.
#[local]
Remove Hints iso_shrink : typeclass_instances.
#[local]
Remove Hints iso_genSized : typeclass_instances.

(* ContractLRecord *)

#[global] 
Instance Contract_Show: Show ContractLRecord.
refine Showprod.
Defined.

#[global] 
Instance Contract_Shrink: Shrink ContractLRecord. 
refine Shrinkprod.
Defined.

#[global] 
Instance Contract_GenSized: GenSized ContractLRecord. 
refine GenSizedprod.
Defined.

(*MessagesAndEvents*)

#[global] 
Instance MessagesAndEvents_Show: Show MessagesAndEventsLRecord.
refine Showxprod.
Defined.

#[global] 
Instance MessagesAndEvents_Shrink: Shrink MessagesAndEventsLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance MessagesAndEvents_GenSized: GenSized MessagesAndEventsLRecord. 
refine GenSizedxprod.
Defined.

(*LocalState*)

#[global] 
Instance LocalState_Show: Show LocalStateLRecord.
refine Showxprod.
Defined.

#[global] 
Instance LocalState_Shrink: Shrink LocalStateLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance LocalState_GenSized: GenSized LocalStateLRecord. 
refine GenSizedxprod.
Defined.

(*Ledger*)

#[global] 
Instance Ledger_Show: Show LedgerLRecord | 0.
refine Showxprod.
Defined.

#[global] 
Instance Ledger_Shrink: Shrink LedgerLRecord  | 0.
refine Shrinkxprod.
Defined.

#[global] 
Instance Ledger_GenSized: GenSized LedgerLRecord | 0 . 
refine GenSizedxprod.
Defined.

(*****************************************************)


#[global] Instance LedgerEq_Dec: forall (l1 l2: LedgerLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
Defined.

#[global] Instance ContractEq_Dec: forall (l1 l2: ContractLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
Defined.

#[global] Instance MessagesEq_Dec: forall (l1 l2: MessagesAndEventsLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
Defined.
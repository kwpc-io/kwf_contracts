Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.

(* Require Import mathcomp.ssreflect.ssreflect. *)
(* From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype. *)

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.Args.CallWithArgsGenerator.

Require Import UrsusStdLib.Cpp.stdTypes.
Require Import UrsusStdLib.Cpp.stdErrors. 
Require Import UrsusStdLib.Cpp.stdFunc.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdUFunc.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmProofs.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import DBlank.Ledger.
Require Import DBlank.ClassTypesNotations.
Require Import DBlank.ClassTypes.
Require Import DBlank.Functions.FuncSig.
Require Import DBlank.Functions.FuncNotations.
Require Import DBlank.Functions.Funcs.

(* Require Import Blank.ClassTypesNotations. *)

Set Typeclasses Iterative Deepening.
(* Set Typeclasses Depth 100. *)

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
(* Local Open Scope string_scope. *)
Local Open Scope xlist_scope.

Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DBlank.QuickChicks.QCEnvironment.
Require Import DBlank.QuickChicks.Props.
Require Import UMLang.ExecGenerator.

Require Import Contracts.ProofsCommon.

Section acknowledgeFinalizeLeft.
Context (pkin : uint256 ) (nonce : uint256) (l: LedgerLRecord).

Definition acknowledgeFinalizeLeft_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    acknowledgeFinalizeLeft_ pkin nonce)) l)}.
  unfold UinterpreterL, acknowledgeFinalizeLeft_, check_investor.
  repeat auto_build_P.
Defined.

Definition acknowledgeFinalizeLeft_err : bool.
  term_of_2 acknowledgeFinalizeLeft_err_P acknowledgeFinalizeLeft_err_P.
Defined.

Definition acknowledgeFinalizeLeft_err_prf : acknowledgeFinalizeLeft_err =
  isError (eval_state (UinterpreterL (
    acknowledgeFinalizeLeft_ pkin nonce)) l).
  proof_of_2 acknowledgeFinalizeLeft_err acknowledgeFinalizeLeft_err_P acknowledgeFinalizeLeft_err_P.
Defined.

Lemma acknowledgeFinalizeLeft_isError_proof : acknowledgeFinalizeLeft_isError_prop pkin nonce l.
Proof.
  unfold acknowledgeFinalizeLeft_isError_prop. rewrite isErrorEq.
  rewrite <- acknowledgeFinalizeLeft_err_prf. unfold acknowledgeFinalizeLeft_err.
  
  unfold acknowledgeFinalizeLeft_requires.

  match goal with |-
    match xBoolIfElse ?cond _ _ with _ => _ end = true <-> ?prp =>
    let H := fresh "H" in
    enough (cond = false <-> prp) as H;
    [ rewrite <- H; clear H; destruct cond;
      [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1
      | simpl; intuition
      ]
    |]
  end.
  - split; intros; discriminate.
  - rewrite isErrorEq. match goal with |- _ <-> ?er = true => introduce er end.
    { unfold UinterpreterL, check_investor. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end; simpl; intuition.
Defined.

Definition acknowledgeFinalizeLeft_exec_P :
  {t | t = exec_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l}.
  unfold UinterpreterL, acknowledgeFinalizeLeft_, check_investor.
  repeat auto_build_P.
Defined.

Definition acknowledgeFinalizeLeft_exec : LedgerLRecord.
  term_of_2 acknowledgeFinalizeLeft_exec_P acknowledgeFinalizeLeft_exec_P.
Defined.

Definition acknowledgeFinalizeLeft_exec_prf : acknowledgeFinalizeLeft_exec =
  exec_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l.
  proof_of_2 acknowledgeFinalizeLeft_exec acknowledgeFinalizeLeft_exec_P acknowledgeFinalizeLeft_exec_P.
Defined.

Definition acknowledgeFinalizeLeft_unconditional_exec : LedgerLRecord.
  pose (l' := acknowledgeFinalizeLeft_exec). unfold acknowledgeFinalizeLeft_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma notifyRight_remove_conditions_helper :
  forall {A1 A} (c1 : bool) (v1 : A1)
  (e1 : ErrorType) (a1 a : A),
  match (xBoolIfElse c1 (ControlValue true v1) (ControlError e1)) with
  | ControlValue _ _ => false
  | ControlReturn _ => false
  | _ => true
  end <> true ->
  (if xBoolIfElse c1 false true then a1 else a) = a.
Proof.
  intros.
  destruct c1. 2:{ exfalso. apply H. reflexivity. }
  simpl. reflexivity.
Defined.

Lemma acknowledgeFinalizeLeft_remove_conditions : (~ (acknowledgeFinalizeLeft_requires pkin nonce l)) ->
  acknowledgeFinalizeLeft_exec = acknowledgeFinalizeLeft_unconditional_exec.
Proof.
  pose proof acknowledgeFinalizeLeft_isError_proof as acknowledgeFinalizeLeft_isError_proof'.
  pose proof acknowledgeFinalizeLeft_err_prf as acknowledgeFinalizeLeft_err_proof'.
  unfold acknowledgeFinalizeLeft_err  in acknowledgeFinalizeLeft_err_proof'.
  unfold acknowledgeFinalizeLeft_isError_prop in  acknowledgeFinalizeLeft_isError_proof'.
  rewrite isErrorEq in acknowledgeFinalizeLeft_isError_proof'.

  intros Hnoreq. 
  rewrite <- acknowledgeFinalizeLeft_isError_proof' in Hnoreq. clear acknowledgeFinalizeLeft_isError_proof'.
  rewrite <- acknowledgeFinalizeLeft_err_proof' in Hnoreq.

  clear acknowledgeFinalizeLeft_err_proof'. unfold acknowledgeFinalizeLeft_exec, acknowledgeFinalizeLeft_unconditional_exec.

  apply (notifyRight_remove_conditions_helper _ _ _ _ _ Hnoreq).
Unshelve. all: let n := numgoals in guard n=0. Admitted.

Lemma acknowledgeFinalizeLeft_exec_proof : acknowledgeFinalizeLeft_exec_prop pkin nonce l.
Proof.

  unfold acknowledgeFinalizeLeft_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- acknowledgeFinalizeLeft_exec_prf,
  acknowledgeFinalizeLeft_remove_conditions in Heql'.
  unfold acknowledgeFinalizeLeft_unconditional_exec in Heql'.
  2:{ assumption. }

  match type of Heql' with _ = exec_state _ (exec_state _ (exec_state _ ?t)) =>
  remember t as l'' end.
  replace (uint2N (toValue (eval_state (sRReader || num_investors_received_ ||) l)))
  with (uint2N (toValue (eval_state (sRReader || num_investors_received_ ||) l''))).
  2:{ rewrite Heql''. destruct l. repeat destruct p. reflexivity. }
  clear Heql'' Hnoreq l. rename l'' into l.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  
  rewrite eql in Heql'. compute in Heql'. rewrite Heql', eql. compute.
  split. reflexivity. destruct x15. reflexivity.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

Lemma acknowledgeFinalizeLeft_noexec_proof : acknowledgeFinalizeLeft_noexec_prop pkin nonce l.
Proof.
  unfold acknowledgeFinalizeLeft_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- acknowledgeFinalizeLeft_exec_prf in Heql'.
  unfold acknowledgeFinalizeLeft_exec in Heql'.
  intros Hnoreq. remember acknowledgeFinalizeLeft_isError_proof as prf. clear Heqprf.
  unfold acknowledgeFinalizeLeft_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- acknowledgeFinalizeLeft_err_prf in Hnoreq.
  unfold acknowledgeFinalizeLeft_err in Hnoreq.
  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l' l; compute; auto
    ]
  end. discriminate Hnoreq.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

End acknowledgeFinalizeLeft.

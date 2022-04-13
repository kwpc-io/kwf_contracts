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

Section acknowledgeDeploy.
Context (giver : address) (nonce : uint256) (l : LedgerLRecord).

Definition acknowledgeDeploy_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l)}.
  unfold UinterpreterL, acknowledgeDeploy_, check_giver.
  repeat auto_build_P.
Defined.

Definition acknowledgeDeploy_err : bool.
  term_of_2 acknowledgeDeploy_err_P acknowledgeDeploy_err_P.
Defined.

Definition acknowledgeDeploy_err_prf : acknowledgeDeploy_err =
  isError (eval_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l).
  proof_of_2 acknowledgeDeploy_err acknowledgeDeploy_err_P acknowledgeDeploy_err_P.
Defined.

Lemma acknowledgeDeploy_isError_proof : acknowledgeDeploy_isError_prop giver nonce l.
Proof.
  unfold acknowledgeDeploy_isError_prop. rewrite isErrorEq.
  rewrite <- acknowledgeDeploy_err_prf. unfold acknowledgeDeploy_err.
  
  unfold acknowledgeDeploy_requires.
  
  repeat (replace (exec_state _ _) with l; [|reflexivity]).

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
    { unfold UinterpreterL, check_giver, new_lvalueL. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end; simpl; intuition.
Defined.

Definition acknowledgeDeploy_exec_P :
  {t | t = exec_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l}.
  unfold UinterpreterL, acknowledgeDeploy_, check_giver.
  do 3 auto_build_P. 5:{ eexists; reflexivity. }
  all: repeat auto_build_P.
Defined.

Definition acknowledgeDeploy_exec : LedgerLRecord.
  term_of_2 acknowledgeDeploy_exec_P acknowledgeDeploy_exec_P.
Defined.

Definition acknowledgeDeploy_exec_prf : acknowledgeDeploy_exec =
  exec_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l.
  proof_of_2 acknowledgeDeploy_exec acknowledgeDeploy_exec_P acknowledgeDeploy_exec_P.
Defined.

Lemma acknowledgeDeploy_exec_proof : acknowledgeDeploy_exec_prop giver nonce l.
Proof.
  destruct l eqn:E. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.

  unfold acknowledgeDeploy_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- E, <- acknowledgeDeploy_exec_prf in Heql'.
  unfold acknowledgeDeploy_exec in Heql'.

  remember acknowledgeDeploy_isError_proof as prf. clear Heqprf.
  unfold acknowledgeDeploy_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- E, <- prf, <- acknowledgeDeploy_err_prf in Hnoreq. clear prf.
  unfold acknowledgeDeploy_err in Hnoreq. subst l.

  (* destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  match goal with |- context [ (?a, ?b)%xprod ] =>
  pose (l_orig := (a, b)%xprod) end. *)

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end.

  clear Hnoreq.
  subst l'. destruct x14. intuition.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

Lemma acknowledgeDeploy_noexec_proof : acknowledgeDeploy_noexec_prop giver nonce l.
Proof.

  unfold acknowledgeDeploy_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- acknowledgeDeploy_exec_prf in Heql'.
  unfold acknowledgeDeploy_exec in Heql'.
  intros Hnoreq. remember acknowledgeDeploy_isError_proof as prf. clear Heqprf.
  unfold acknowledgeDeploy_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- acknowledgeDeploy_err_prf in Hnoreq.
  unfold acknowledgeDeploy_err in Hnoreq.

  generalize Heql' Hnoreq. clear Heql' Hnoreq.

  refine (match l with ((x, (x0, (x1, (x2, (x3, (x4, (x5, (x6,
  (x7, (x8, (x9, (x10, (x11, (x12, (x13, (x14, (x15, (x16, x17))))))))))))))))))%core,
  (c0, (m, (m0, (x18, (x19,
  (x20, (a, (x21, (x22, (a0, (c, (c1, (x23, (x24, (c2, (x25, x26)))))))))))),
  (l0, l1))))))%xprod => _ end).

  intros.

  (* assert (l = ((x, (x0, (x1, (x2, (x3, (x4, (x5, (x6,
  (x7, (x8, (x9, (x10, (x11, (x12, (x13, (x14, (x15, (x16, x17))))))))))))))))))%core,
  (c0, (m, (m0, (x18, (x19,
  (x20, (a, (x21, (x22, (a0, (c, (c1, (x23, (x24, (c2, (x25, x26)))))))))))),
  (l0, l1))))))%xprod). 
  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  Show Proof. *)
  
  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l'; compute; reflexivity
    ]
  end. discriminate Hnoreq.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

End acknowledgeDeploy.

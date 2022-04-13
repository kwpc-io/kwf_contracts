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


Section setFromGiverCodeHash.
Context (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) ( l: LedgerLRecord ).

Definition setFromGiverCodeHash_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l)}.
  unfold UinterpreterL, setFromGiverCodeHash_, check_owner.
  repeat auto_build_P.
Defined.

Definition setFromGiverCodeHash_err : bool.
  term_of_2 setFromGiverCodeHash_err_P setFromGiverCodeHash_err_P.
Defined.

Definition setFromGiverCodeHash_err_prf : setFromGiverCodeHash_err =
  isError (eval_state (UinterpreterL (
    setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l).
  proof_of_2 setFromGiverCodeHash_err setFromGiverCodeHash_err_P setFromGiverCodeHash_err_P.
Defined.

Lemma setFromGiverCodeHash_isError_proof : setFromGiverCodeHash_isError_prop eb code_hash code_depth l.
Proof.
  unfold setFromGiverCodeHash_isError_prop. rewrite isErrorEq.
  rewrite <- setFromGiverCodeHash_err_prf. unfold setFromGiverCodeHash_err.
  
  unfold setFromGiverCodeHash_requires.
  
  repeat (replace (exec_state _ _) with l; [|reflexivity]).
  
  match goal with |-
    match xBoolIfElse ?cond _ _ with _ => _ end = true <-> (?prp \/ _) \/ _ =>
    let H := fresh "H" in
    enough (cond = false <-> prp) as H;
    [ rewrite <- H; clear H; destruct cond;
      [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1;
        match goal with |- context [ true = false \/ ?P ] =>
          rewrite (elim_left_absurd P)
        end
      | simpl; intuition
      ]
    |]
  end.

  do 3 match goal with
  | |- _ <-> _ =>
    match goal with |-
      match xBoolIfElse ?cond _ _ with _ => _ end = true <-> ?prp \/ _ =>
      let H := fresh "H" in
      enough (cond = false <-> prp) as H;
      [ rewrite <- H; clear H; destruct cond;
        [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1;
          match goal with |- context [ true = false \/ ?P ] =>
            rewrite (elim_left_absurd P)
          end
        | simpl; intuition
        ]
      |]
    end
  | |- _ => idtac
  end.

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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N eb =>
      replace tv1 with (xIntGeb tv2 eb);
      [destruct tv2; destruct eb|reflexivity]
    end.
    simpl. rewrite N.leb_gt. reflexivity.
  - reflexivity.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
      replace tv1 with (Common.eqb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. reflexivity.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
      replace tv1 with (boolNegb (Common.eqb tv2 (Build_XUBInteger (n:=256) 0)));
      [destruct tv2|reflexivity]
    end.
    simpl. destruct (N.eqb_spec x 0); split; intros; lia.
Defined.

Definition setFromGiverCodeHash_exec_P :
  {t | t = exec_state (UinterpreterL (
    setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l}.
  unfold UinterpreterL, setFromGiverCodeHash_, check_owner.
  repeat auto_build_P.
Defined.

Definition setFromGiverCodeHash_exec : LedgerLRecord.
  term_of_2 setFromGiverCodeHash_exec_P setFromGiverCodeHash_exec_P.
Defined.

Definition setFromGiverCodeHash_exec_prf : setFromGiverCodeHash_exec =
  exec_state (UinterpreterL (
    setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l.
  proof_of_2 setFromGiverCodeHash_exec setFromGiverCodeHash_exec_P setFromGiverCodeHash_exec_P.
Defined.

Lemma setFromGiverCodeHash_exec_proof : setFromGiverCodeHash_exec_prop eb code_hash code_depth l.
Proof.
  unfold setFromGiverCodeHash_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) l) as l'.
  rewrite <- setFromGiverCodeHash_exec_prf in Heql'.
  unfold setFromGiverCodeHash_exec in Heql'.

  remember setFromGiverCodeHash_isError_proof as prf. clear Heqprf.
  unfold setFromGiverCodeHash_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf, <- setFromGiverCodeHash_err_prf in Hnoreq. clear prf.
  unfold setFromGiverCodeHash_err in Hnoreq.

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end.

  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  compute in Heql'.
  subst l'. compute.
  destruct code_hash. destruct code_depth. intuition.
Defined.

Lemma setFromGiverCodeHash_noexec_proof : setFromGiverCodeHash_noexec_prop eb code_hash code_depth l.
Proof.
  unfold setFromGiverCodeHash_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- setFromGiverCodeHash_exec_prf in Heql'.
  unfold setFromGiverCodeHash_exec in Heql'.
  intros Hnoreq. remember setFromGiverCodeHash_isError_proof as prf. clear Heqprf.
  unfold setFromGiverCodeHash_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- setFromGiverCodeHash_err_prf in Hnoreq.
  unfold setFromGiverCodeHash_err in Hnoreq.
  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l'; compute; reflexivity
    ]
  end. discriminate Hnoreq.
Defined.
  
End setFromGiverCodeHash.

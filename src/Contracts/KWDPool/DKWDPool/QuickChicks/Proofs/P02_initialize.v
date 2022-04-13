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
Require Import DKWDPool.Ledger.
Require Import DKWDPool.ClassTypesNotations.
Require Import DKWDPool.ClassTypes.
Require Import DKWDPool.Functions.FuncSig.
Require Import DKWDPool.Functions.FuncNotations.
Require Import DKWDPool.Functions.Funcs.

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
Require Import DKWDPool.QuickChicks.QCEnvironment.
Require Import DKWDPool.QuickChicks.Props.
Require Import UMLang.ExecGenerator.

Require Import Contracts.ProofsCommon.

Section initialize.
Context (lock_time :  uint32 ) (unlock_time :  uint32 )
(quant : ( XUInteger128 )) (rate : ( XUInteger8 ))
(kwf_lock_time : ( XUInteger32 ))  ( l: LedgerLRecord ).

Definition initialize_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    initialize_ lock_time unlock_time quant rate kwf_lock_time)) l)}.
  unfold UinterpreterL, initialize_, check_fund.
  repeat auto_build_P.
Defined.

Definition initialize_err : bool.
  term_of_2 initialize_err_P initialize_err_P.
Defined.

Definition initialize_err_prf : initialize_err =
  isError (eval_state (UinterpreterL (
    initialize_ lock_time unlock_time quant rate kwf_lock_time)) l).
  proof_of_2 initialize_err initialize_err_P initialize_err_P.
Defined.

Lemma initialize_isError_proof : initialize_isError_prop lock_time unlock_time quant rate kwf_lock_time l.
Proof.
  unfold initialize_isError_prop. rewrite isErrorEq.
  rewrite <- initialize_err_prf. unfold initialize_err.
  
  unfold initialize_requires.
  
  repeat (replace (exec_state _ _) with l; [|reflexivity]).
  
  (* match goal with |-
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
  end. *)

  do 4 match goal with
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 >= _ =>
    replace tv1 with (Common.ltb tv2 lock_time);
    [destruct tv2; destruct lock_time|reflexivity] end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> ?tv2 = true =>
    replace tv1 with (negb tv2); [destruct tv2|reflexivity] end;
    simpl; split; intros; congruence.
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. destruct (Z.eqb_spec x x1). 2:{ split; intros; simpl in *; congruence. }
    destruct x0. destruct x2. simpl.
    destruct (N.eqb_spec x0 x2); split; intros; simpl in *; congruence.
Defined.


End initialize.
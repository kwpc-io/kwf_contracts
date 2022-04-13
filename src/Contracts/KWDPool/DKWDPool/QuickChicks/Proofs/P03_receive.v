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

Section receive.
Context (DMF : uint16) ( GFM  : uint128) (  EB : uint128) ( l: LedgerLRecord ).

Definition receive_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    receive_ ( KWMessages_ι_DEFAULT_MSG_FLAGS_ := DMF) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l)}.
  unfold UinterpreterL, receive_, check_init.
  do 6 auto_build_P. 5:{ eexists; reflexivity. } all: repeat auto_build_P.
Defined.

Definition receive_err : bool.
  term_of_2 receive_err_P receive_err_P.
Defined.

Definition receive_err_prf : receive_err =
  isError (eval_state (UinterpreterL (
    receive_ ( KWMessages_ι_DEFAULT_MSG_FLAGS_ := DMF) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l).
  proof_of_2 receive_err receive_err_P receive_err_P.
Defined.

Lemma receive_isError_proof : receive_isError_prop DMF GFM EB l.
Proof.
  unfold receive_isError_prop. rewrite isErrorEq.
  rewrite <- receive_err_prf. unfold receive_err.
  
  unfold receive_requires.
  
  do 4 (replace (exec_state _ _) with l; [|reflexivity]).
  
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

  do 1 match goal with
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

  lazymatch goal with
  | |- _ <-> _ =>
    lazymatch goal with |-
      match xBoolIfElse ?cond _ _ with _ => _ end = true <-> ?prp /\ _ =>
      let H := fresh "H" in
      enough (cond = true <-> prp) as H;
      [ rewrite <- H; clear H; destruct cond;
        [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1
        | simpl; intuition
        ]
      |]
    end
  | |- _ => idtac
  end.

  assert (forall P Q : Prop, P -> (P /\ Q) <-> Q) as tmp.
  { intros P Q p. split.
    - intros [_ q]. apply q.
    - intros q. split; auto.
  }
  match goal with |- context [ true = true /\ ?P ] =>
    rewrite (tmp (true = true) P); [|reflexivity]
  end. clear tmp.

  repeat match goal with
  | |- _ <-> _ =>
    match goal with |- match (right_orify_result false
      match xBoolIfElse ?cond _ _ with _ => _ end)
      with _ => _ end = true <-> ?prp \/ _ =>
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

  match goal with
  | |- _ <-> _ =>
    match goal with |- match (right_orify_result false (left_orify_result true
      match xBoolIfElse ?cond _ _ with _ => _ end))
      with _ => _ end = true <-> ?prp \/ _ =>
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

  match goal with
  | |- _ <-> _ =>
    match goal with |- match (right_orify_result false (left_orify_result true
      (left_orify_result true
      match xBoolIfElse ?cond _ _ with _ => _ end)))
      with _ => _ end = true <-> ?prp =>
      let H := fresh "H" in
      enough (cond = false <-> prp) as H;
      [ rewrite <- H; clear H; destruct cond;
        [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1
        | simpl; intuition
        ]
      |]
    end
  | |- _ => idtac
  end.

  match goal with |- match (_ _ (_ _ (_ _ (_ _ ?a))))
  with _ => _ end = true <-> _ =>
  remember a as y end.
  dependent destruction y. simpl.
  - split; intros; discriminate.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
    replace tv1 with (Common.ltb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 + _ =>
    replace tv1 with (xIntGeb tv2 (xIntPlus (xIntPlus tv3 GFM) EB));
    [destruct tv2; destruct tv3; destruct GFM; destruct EB|reflexivity] end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 =>
    replace tv1 with (xIntGeb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = true <-> uint2N ?tv2 = 0 =>
    replace tv1 with (Common.eqb tv2 (Build_XUBInteger 0));
    [destruct tv2|reflexivity] end.
    simpl. rewrite N.eqb_eq. reflexivity.
  - reflexivity.
Defined.

End receive.
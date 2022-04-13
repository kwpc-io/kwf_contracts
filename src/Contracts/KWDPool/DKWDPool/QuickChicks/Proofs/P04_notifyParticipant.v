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

Section notifyParticipant.
Context (  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 )
(summa_givers :  uint128 ) ( l: LedgerLRecord ).

Definition notifyParticipant_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    notifyParticipant_ (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l)}.
  unfold UinterpreterL, notifyParticipant_, check_init, check_fund.
  repeat auto_build_P.
Defined.

Definition notifyParticipant_err : bool.
  term_of_2 notifyParticipant_err_P notifyParticipant_err_P.
Defined.

Definition notifyParticipant_err_prf : notifyParticipant_err =
  isError (eval_state (UinterpreterL (
    notifyParticipant_ (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l).
  proof_of_2 notifyParticipant_err notifyParticipant_err_P notifyParticipant_err_P.
Defined.

Lemma notifyParticipant_isError_proof : notifyParticipant_isError_prop EB giveup summa_investors summa_givers l.
Proof.
  unfold notifyParticipant_isError_prop. rewrite isErrorEq.
  rewrite <- notifyParticipant_err_prf. unfold notifyParticipant_err.
  
  unfold notifyParticipant_requires.
  
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

  match goal with
  | |- _ <-> _ =>
    match goal with |-
      match xBoolIfElse ?cond _ _ with _ => _ end = true <-> ?prp \/ _ =>
      let H := fresh "H" in
      enough (match cond with Some _ => False | _ => True end <-> prp) as H;
      [ rewrite <- H; clear H; destruct cond;
        [|simpl; intuition
        ]
      |]
    end
  end.
  assert (forall P, False \/ P <-> P) as tmp. { intros. split; intros H.
    destruct H. destruct H. assumption. right. assumption. }
  rewrite tmp. clear tmp.
  unfold xBoolIfElse at 1, maybeFunBool at 1, maybeFunRec at 1,
    Common.maybeFunBool_obligation_3 at 1, xBoolIfElse at 1,
    boolFunRec at 1, xMaybeIsNone at 1, isNone at 1.

  do 2 match goal with
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 + uint2N ?tv4 + uint2N EB =>
    replace tv1 with (xIntGeb tv2 (xIntPlus (xIntPlus tv3 tv4) EB));
    [destruct tv2; destruct tv3; destruct tv4; destruct EB|reflexivity] end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <= 0 =>
    replace tv1 with (xIntGtb tv2 (Build_XUBInteger 0));
    [destruct tv2|reflexivity] end.
    simpl. rewrite N.ltb_ge. lia.
  - destruct (toValue _); split; intros; auto. destruct H. discriminate H.
  - match goal with |- ?tv1 = false <-> ?tv2 = true =>
    replace tv1 with (negb tv2); [destruct tv2|reflexivity] end;
    simpl; split; intros; congruence.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 \/ uint2N ?tv2 > uint2N ?tv4 =>
    replace tv1 with (andb (xIntGeb tv2 tv3) (xIntLeb tv2 tv4));
    [destruct tv2; destruct tv3; destruct tv4|reflexivity] end.
    simpl. rewrite Bool.andb_false_iff, N.leb_gt, N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. destruct (Z.eqb_spec x x1). 2:{ split; intros; congruence. }
    destruct x0. destruct x2. simpl. rewrite N.eqb_neq.
    split; intros; congruence.
  - reflexivity.
Defined.
  
End notifyParticipant.
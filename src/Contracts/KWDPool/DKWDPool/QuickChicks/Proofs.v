Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Bool. 
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

Require Import UrsusStdLib.Cpp.stdTypes.
Require Import UrsusStdLib.Cpp.stdErrors. 
Require Import UrsusStdLib.Cpp.stdFunc.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdUFunc.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

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
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DKWDPool.QuickChicks.QCEnvironment.
Require Import DKWDPool.QuickChicks.Props.
Require Import DKWDPool.QuickChicks.Generators.

Set Typeclasses Iterative Deepening.
(* Set Typeclasses Depth 100. *)

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DKWDPool.QuickChicks.QCEnvironment.

Import FinProof.Common.  (*for eqb!!!*)
Require Import FinProof.CommonInstances.
Require Import UMLang.ExecGenerator.

Lemma elim_left_absurd : forall P : Prop,
  true = false \/ P <-> P.
Proof.
  intros P. split; intros H.
  - destruct H as [H|H]. discriminate H. apply H.
  - right. apply H.
Defined.

Lemma elim_left_refl : forall (a : bool) (P : Prop),
  a = a /\ P <-> P.
  intros. split; intros H.
  - destruct H. assumption.
  - split. reflexivity. assumption.
Defined.

Lemma isErrorEq : forall {R b} (cr : ControlResult R b),
  CommonQCEnvironment.isError cr <-> isError cr = true.
Proof. unfold isError, CommonQCEnvironment.isError. destruct cr; intuition. Defined.

Section constructor.
Context ( MB: uint128 ) ( GFM: uint128 )
( final_address: optional address ) ( l: LedgerLRecord ) .

Definition constructor_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    constructor_ (KWD_MIN_BALANCE_:= MB) (GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l)}.
  unfold UinterpreterL, constructor_, check_owner.
  repeat auto_build_P.
Defined.

Definition constructor_err : bool.
  term_of_2 constructor_err_P constructor_err_P.
Defined.

Definition constructor_err_prf : constructor_err =
  isError (eval_state (UinterpreterL (
    constructor_ (KWD_MIN_BALANCE_:= MB) (GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l).
  proof_of_2 constructor_err constructor_err_P constructor_err_P.
Defined.

Lemma constructor_isError_proof : constructor_isError_prop MB GFM final_address l.
Proof.
  unfold constructor_isError_prop. rewrite isErrorEq.
  rewrite <- constructor_err_prf. unfold constructor_err.
  
  unfold constructor_requires.
  
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
  - match goal with |- ?tv1 = false <-> ?tv2 = default =>
    replace tv1 with (negb (Common.eqb tv2 default)); [destruct tv2|reflexivity] end.
    simpl. destruct (Z.eqb_spec x 0). 2:{ split; intros; simpl in *; congruence. }
    destruct x0. simpl. destruct (N.eqb_spec x0 0); split; intros; simpl in *; congruence.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < _ =>
    replace tv1 with (xIntGeb tv2 (xIntPlus MB GFM));
    [destruct tv2; destruct MB; destruct GFM|reflexivity] end.
    simpl. apply N.leb_gt.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3); [destruct tv2; destruct tv3|reflexivity] end.
    simpl. apply N.eqb_neq.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
    replace tv1 with (negb (Common.eqb tv2 (Build_XUBInteger 0)));
    [destruct tv2|reflexivity] end.
    simpl. destruct (N.eqb_spec x 0); simpl; split; intros; congruence.
Defined.
  
End constructor.



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
    replace tv1 with (ltb tv2 lock_time);
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



Section receive.
Context (DMF : uint16) ( GFM  : uint128) (  EB : uint128) ( l: LedgerLRecord ).

Definition receive_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    receive_ ( DEFAULT_MSG_FLAGS_ := DMF) (GAS_FOR_FUND_MESSAGE_ := GFM) (EPSILON_BALANCE_ := EB) )) l)}.
  unfold UinterpreterL, receive_, check_init.
  repeat auto_build_P.
Defined.

Definition receive_err : bool.
  term_of_2 receive_err_P receive_err_P.
Defined.

Definition receive_err_prf : receive_err =
  isError (eval_state (UinterpreterL (
    receive_ ( DEFAULT_MSG_FLAGS_ := DMF) (GAS_FOR_FUND_MESSAGE_ := GFM) (EPSILON_BALANCE_ := EB) )) l).
  proof_of_2 receive_err receive_err_P receive_err_P.
Defined.

Lemma receive_isError_proof : receive_isError_prop DMF GFM EB l.
Proof.
  unfold receive_isError_prop. rewrite isErrorEq.
  rewrite <- receive_err_prf. unfold receive_err.
  
  unfold receive_requires.
  
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

  do 1 match goal with
  | |- _ <-> _ =>
    match goal with
      | |- match xBoolIfElse ?cond _ _ with _ => _ end = true
      <-> ?prp \/ _ =>
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

  match goal with |- xBoolIfElse ?cond _ _ = true <-> ?prp /\ _ =>
  let H := fresh "H" in
  enough (cond = true <-> prp) as H; [rewrite <- H; clear H;
  destruct cond; [|intuition] |] end.
  unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1.
  rewrite elim_left_refl.

  do 3 match goal with
  | |- _ <-> _ =>
    match goal with
      | |- match xBoolIfElse ?cond _ _ with _ => _ end = true
      <-> ?prp \/ _ =>
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



Section notifyParticipant.
Context (  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 )
(summa_givers :  uint128 ) ( l: LedgerLRecord ).

Definition notifyParticipant_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    notifyParticipant_ (EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l)}.
  unfold UinterpreterL, notifyParticipant_, check_init, check_fund.
  repeat auto_build_P.
Defined.

Definition notifyParticipant_err : bool.
  term_of_2 notifyParticipant_err_P notifyParticipant_err_P.
Defined.

Definition notifyParticipant_err_prf : notifyParticipant_err =
  isError (eval_state (UinterpreterL (
    notifyParticipant_ (EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l).
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



Section setFinalAddress.
Context (EB :  uint128) ( final_address:  address ) ( l: LedgerLRecord ).

Definition setFinalAddress_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    setFinalAddress_ (EPSILON_BALANCE_ := EB) final_address)) l)}.
  unfold UinterpreterL, setFinalAddress_, check_owner, check_init.
  repeat auto_build_P.
Defined.

Definition setFinalAddress_err : bool.
  term_of_2 setFinalAddress_err_P setFinalAddress_err_P.
Defined.

Definition setFinalAddress_err_prf : setFinalAddress_err =
  isError (eval_state (UinterpreterL (
    setFinalAddress_ (EPSILON_BALANCE_ := EB) final_address)) l).
  proof_of_2 setFinalAddress_err setFinalAddress_err_P setFinalAddress_err_P.
Defined.

Lemma setFinalAddress_isError_proof : setFinalAddress_isError_prop EB final_address l.
Proof.
  unfold setFinalAddress_isError_prop. rewrite isErrorEq.
  rewrite <- setFinalAddress_err_prf. unfold setFinalAddress_err.
  
  unfold setFinalAddress_requires.
  
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 + uint2N EB =>
    replace tv1 with (xIntGeb tv2 (xIntPlus tv3 EB));
    [destruct tv2; destruct tv3; destruct EB|reflexivity] end.
    simpl. apply N.leb_gt.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. apply N.eqb_neq.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
    replace tv1 with (negb (Common.eqb tv2 (Build_XUBInteger 0)));
    [destruct tv2|reflexivity] end.
    simpl. destruct (N.eqb_spec x 0); simpl; split; intros; congruence.
  - reflexivity.
Defined.
End setFinalAddress.



Section returnFunds.
Context (EB : uint128) (address_to :  address  ) ( l: LedgerLRecord ).

Definition returnFunds_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    returnFunds_ (EPSILON_BALANCE_ := EB) address_to)) l)}.
  unfold UinterpreterL, returnFunds_, check_owner, check_init.
  repeat auto_build_P.
Defined.

Definition returnFunds_err : bool.
  term_of_2 returnFunds_err_P returnFunds_err_P.
Defined.

Definition returnFunds_err_prf : returnFunds_err =
  isError (eval_state (UinterpreterL (
    returnFunds_ (EPSILON_BALANCE_ := EB) address_to)) l).
  proof_of_2 returnFunds_err returnFunds_err_P returnFunds_err_P.
Defined.

Lemma returnFunds_isError_proof : returnFunds_isError_prop EB address_to l.
Proof.
  unfold returnFunds_isError_prop. rewrite isErrorEq.
  rewrite <- returnFunds_err_prf. unfold returnFunds_err.
  
  unfold returnFunds_requires.
  
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N EB =>
    replace tv1 with (xIntGeb tv2 EB);
    [destruct tv2; destruct EB|reflexivity] end.
    simpl. apply N.leb_gt.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <= uint2N ?tv3 /\ ?tv4 = true =>
    replace tv1 with (orb (xIntGtb tv2 tv3) (negb tv4));
    [destruct tv2; destruct tv3; destruct tv4|reflexivity] end; simpl.
    2:{ rewrite right_or_true. split; intros H. discriminate H. destruct H. discriminate. }
    rewrite right_or_false, N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> _ = ?tv2 =>
    replace tv1 with (negb (Common.eqb address_to tv2));
    [destruct tv2; destruct address_to|reflexivity] end.
    simpl. destruct x2. destruct x0. simpl.
    destruct (Z.eqb_spec x1 x). 2:{ simpl. split; intros; congruence. }
    destruct (N.eqb_spec x2 x0); simpl; split; intros; congruence.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. rewrite N.eqb_neq. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
    replace tv1 with (negb (Common.eqb tv2 (Build_XUBInteger 0)));
    [destruct tv2|reflexivity] end.
    simpl. destruct (N.eqb_spec x 0); simpl; split; intros; congruence.
Defined.
  
End returnFunds.



Section acknowledgeFunds.
Context (l : LedgerLRecord).

Definition acknowledgeFunds_err_P :
{t | t = isError (eval_state (UinterpreterL (
  acknowledgeFunds_)) l)}.
  unfold UinterpreterL, acknowledgeFunds_, check_owner, check_init, check_fund.
  repeat auto_build_P.
Defined.

Definition acknowledgeFunds_err : bool.
  term_of_2 acknowledgeFunds_err_P acknowledgeFunds_err_P.
Defined.

Definition acknowledgeFunds_err_prf : acknowledgeFunds_err =
  isError (eval_state (UinterpreterL (
    acknowledgeFunds_)) l).
  proof_of_2 acknowledgeFunds_err acknowledgeFunds_err_P acknowledgeFunds_err_P.
Defined.

Lemma acknowledgeFunds_isError_proof : acknowledgeFunds_isError_prop l.
Proof.
  unfold acknowledgeFunds_isError_prop. rewrite isErrorEq.
  rewrite <- acknowledgeFunds_err_prf. unfold acknowledgeFunds_err.
  
  unfold acknowledgeFunds_requires.
  
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
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. destruct (Z.eqb_spec x x1). 2:{ split; intros; congruence. }
    destruct x0. destruct x2. simpl. rewrite N.eqb_neq.
    split; intros; congruence.
  - reflexivity.
Defined.

End acknowledgeFunds.



Section returnExtraFunds.
Context (MB : uint128) (EB :uint128 ) (address_to : address ) ( l: LedgerLRecord ).

Definition returnExtraFunds_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    returnExtraFunds_ (KWD_MIN_BALANCE_ := MB) (EPSILON_BALANCE_ := EB) address_to)) l)}.
  unfold UinterpreterL, returnExtraFunds_, check_owner, check_init.
  repeat auto_build_P.
Defined.

Definition returnExtraFunds_err : bool.
  term_of_2 returnExtraFunds_err_P returnExtraFunds_err_P.
Defined.

Definition returnExtraFunds_err_prf : returnExtraFunds_err =
  isError (eval_state (UinterpreterL (
    returnExtraFunds_ (KWD_MIN_BALANCE_ := MB) (EPSILON_BALANCE_ := EB) address_to)) l).
  proof_of_2 returnExtraFunds_err returnExtraFunds_err_P returnExtraFunds_err_P.
Defined.

Lemma returnExtraFunds_isError_proof : returnExtraFunds_isError_prop MB EB address_to l.
Proof.
  unfold returnExtraFunds_isError_prop. rewrite isErrorEq.
  rewrite <- returnExtraFunds_err_prf. unfold returnExtraFunds_err.
  
  unfold returnExtraFunds_requires.
  
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

  repeat match goal with
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. rewrite N.eqb_neq. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
    replace tv1 with (negb (Common.eqb tv2 (Build_XUBInteger 0)));
    [destruct tv2|reflexivity] end.
    simpl. destruct (N.eqb_spec x 0); simpl; split; intros; congruence.
Defined.
  
End returnExtraFunds.



Section sendFunds.
Context (EB: uint128) (address_to :  address  ) ( l: LedgerLRecord ).

Definition sendFunds_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    sendFunds_ (EPSILON_BALANCE_ := EB) address_to)) l)}.
  unfold UinterpreterL, sendFunds_, check_owner, check_init, check_fund.
  repeat auto_build_P.
Defined.

Definition sendFunds_err : bool.
  term_of_2 sendFunds_err_P sendFunds_err_P.
Defined.

Definition sendFunds_err_prf : sendFunds_err =
  isError (eval_state (UinterpreterL (
    sendFunds_ (EPSILON_BALANCE_ := EB) address_to)) l).
  proof_of_2 sendFunds_err sendFunds_err_P sendFunds_err_P.
Defined.

Lemma sendFunds_isError_proof : sendFunds_isError_prop EB address_to l.
Proof.
  unfold sendFunds_isError_prop. rewrite isErrorEq.
  rewrite <- sendFunds_err_prf. unfold sendFunds_err.
  
  unfold sendFunds_requires.
  
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

  repeat match goal with
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
  idtac.
  lazymatch goal with
  | |- _ <-> _ =>
    lazymatch goal with |-
      match xBoolIfElse ?cond _ _ with _ => _ end = true <-> ?prp \/ _ =>
      let H := fresh "H" in
      enough (xBoolIfElse cond true false = false <-> prp) as H;
      [ rewrite <- H; clear H; destruct cond;
        [ 
          lazymatch goal with |- match xBoolIfElse ?c _ _ with _ => _ end = _ <-> _ =>
            do 2 first [
              lazymatch goal with |- context [ xBoolIfElse c ?tr ?fs ] =>
                replace (xBoolIfElse c tr fs) with fs; [|reflexivity]
              end
            | lazymatch goal with |- context [ xBoolIfElse c ?tr ?fs ] =>
                replace (xBoolIfElse c tr fs) with tr; [|reflexivity]
              end
            ]
          end;
          lazymatch goal with |- context [ true = false \/ ?P ] =>
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
    simpl. apply N.leb_gt.
  - destruct (toValue _); simpl; [split; intros; discriminate | split; intros; reflexivity].
  - reflexivity.
  - match goal with |- ?tv1 = false <-> _ = ?tv2 =>
    replace tv1 with (negb (Common.eqb address_to tv2));
    [destruct tv2; destruct address_to|reflexivity] end.
    simpl. destruct x2. destruct x0. simpl.
    destruct (Z.eqb_spec x1 x). 2:{ simpl. split; intros; congruence. }
    destruct (N.eqb_spec x2 x0); simpl; split; intros; congruence.
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. destruct x2. destruct x0. simpl.
    destruct (Z.eqb_spec x x1). 2:{ simpl. split; intros; congruence. }
    destruct (N.eqb_spec x0 x2); simpl; split; intros; congruence.
  - reflexivity.
Defined.
  
End sendFunds.



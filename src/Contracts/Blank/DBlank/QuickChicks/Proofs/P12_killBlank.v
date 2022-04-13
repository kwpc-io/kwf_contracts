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

Section killBlank.
Context (eb: uint128) (address_to: address) (l: LedgerLRecord ).

Definition killBlank_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l)}.
  unfold UinterpreterL, killBlank_, check_owner.
  repeat auto_build_P.
Defined.

Definition killBlank_err : bool.
  term_of_2 killBlank_err_P killBlank_err_P.
Defined.

Definition killBlank_err_prf : killBlank_err =
  isError (eval_state (UinterpreterL (
    killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l).
  proof_of_2 killBlank_err killBlank_err_P killBlank_err_P.
Defined.

Lemma killBlank_isError_proof : killBlank_isError_prop eb address_to l.
Proof.
  unfold killBlank_isError_prop. rewrite isErrorEq.
  rewrite <- killBlank_err_prf. unfold killBlank_err.
  
  unfold killBlank_requires.
  
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N eb =>
      replace tv1 with (xIntGeb tv2 eb);
      [destruct tv2; destruct eb|reflexivity]
    end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <= uint2N ?tv3 =>
      replace tv1 with (xIntGtb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> address_to = ?tv2 =>
      replace tv1 with (boolNegb (Common.eqb address_to tv2));
      [destruct tv2; destruct address_to|reflexivity]
    end.
    destruct x2. destruct x0. simpl. destruct (Z.eqb_spec x1 x).
    2:{ split; intros; congruence. }
    destruct (N.eqb_spec x2 x0); split; intros; congruence.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
      replace tv1 with (Common.eqb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. split; intros n H; congruence.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
      replace tv1 with (boolNegb (Common.eqb tv2 (Build_XUBInteger 0)));
      [destruct tv2|reflexivity]
    end.
    simpl. destruct (N.eqb_spec x 0); split; intros; congruence.
Defined.

Definition killBlank_exec_P :
  {t | t = exec_state (UinterpreterL (killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l}.
  unfold UinterpreterL, killBlank_, check_owner.
  repeat auto_build_P.
Defined.

Definition killBlank_exec : LedgerLRecord.
  term_of_2 killBlank_exec_P killBlank_exec_P.
Defined.

Definition killBlank_exec_prf : killBlank_exec =
  exec_state (UinterpreterL (killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l.
  proof_of_2 killBlank_exec killBlank_exec_P killBlank_exec_P.
Defined.

Definition killBlank_unconditional_exec : LedgerLRecord.
  pose (l' := killBlank_exec). unfold killBlank_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma notifyRight_remove_conditions_helper :
  forall {A1 A2 A3 A4 A5 A} (c1 c2 c3 c4 c5 : bool) (v1 : A1) (v2 : A2) (v3 : A3) (v4 : A4) (v5 : A5)
  (e1 e2 e3 e4 e5 : ErrorType) (a1 a2 a3 a4 a5 a : A),
  match (xBoolIfElse c1 (ControlValue true v1) (ControlError e1)) with
  | ControlValue _ _ => match (xBoolIfElse c2 (ControlValue true v2) (ControlError e2)) with
  | ControlValue _ _ => match (xBoolIfElse c3 (ControlValue true v3) (ControlError e3)) with
  | ControlValue _ _ => match (xBoolIfElse c4 (ControlValue true v4) (ControlError e4)) with
  | ControlValue _ _ => match (xBoolIfElse c5 (ControlValue true v5) (ControlError e5)) with
  | ControlValue _ _ => false
  | ControlReturn _ => false
  | _ => true
  end
  | ControlReturn _ => false
  | _ => true
  end
  | ControlReturn _ => false
  | _ => true
  end
  | ControlReturn _ => false
  | _ => true
  end
  | ControlReturn _ => false
  | _ => true
  end <> true ->
  (if xBoolIfElse c1 false true then a1 else
  if xBoolIfElse c2 false true then a2 else
  if xBoolIfElse c3 false true then a3 else
  if xBoolIfElse c4 false true then a4 else
  if xBoolIfElse c5 false true then a5 else a) = a.
Proof.
  intros.
  destruct c1. 2:{ exfalso. apply H. reflexivity. }
  destruct c2. 2:{ exfalso. apply H. reflexivity. }
  destruct c3. 2:{ exfalso. apply H. reflexivity. }
  destruct c4. 2:{ exfalso. apply H. reflexivity. }
  destruct c5. 2:{ exfalso. apply H. reflexivity. }
  simpl. reflexivity.
Defined.

Lemma killBlank_remove_conditions : (~ (killBlank_requires eb address_to l)) ->
  killBlank_exec = killBlank_unconditional_exec.
Proof.
  pose proof killBlank_isError_proof as killBlank_isError_proof'.
  pose proof killBlank_err_prf as killBlank_err_proof'.
  unfold killBlank_err  in killBlank_err_proof'.
  unfold killBlank_isError_prop in  killBlank_isError_proof'.
  rewrite isErrorEq in killBlank_isError_proof'.

  intros Hnoreq. 
  rewrite <- killBlank_isError_proof' in Hnoreq. clear killBlank_isError_proof'.
  rewrite <- killBlank_err_proof' in Hnoreq.

  clear killBlank_err_proof'. unfold killBlank_exec, killBlank_unconditional_exec.

  apply (notifyRight_remove_conditions_helper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnoreq).
Defined.

Lemma killBlank_exec_proof : killBlank_exec_prop eb address_to l.
Proof.

  unfold killBlank_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- killBlank_exec_prf,
  killBlank_remove_conditions in Heql'.
  unfold killBlank_unconditional_exec in Heql'.
  2:{ assumption. }

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  destruct m. repeat destruct p.

  match type of Heql' with _ = exec_state _ ?t => remember t as pre_suic end.

  Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.
  rewrite eql in Heqpre_suic. compute in Heqpre_suic.
  Transparent xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.

  (* match type of Heql' with _ = ?t => introduce t end.
  {
    unfold suicide_left, wrapULExpression, SML_NG32.wrapULExpression.
    auto_build_P. unfold UExpressionP_Next_LedgerableWithRArgsL,
    UExpressionP0_LedgerableWithArgsL, ursus_call_with_argsL.
    C_r_exec_P. auto_build_P. auto_build_P.
    unfold suicide, tvm_transfer_left.
    unfold wrapULExpression, SML_NG32.wrapULExpression. do 2 auto_build_P.
    all: only 2, 3, 4: repeat auto_build_P.
    unfold UExpressionP_Next_LedgerableWithRArgsL,
    UExpressionP0_LedgerableWithArgsL, ursus_call_with_argsL.
    C_rrrr_exec_P.
    8:{
      Check SEND_ALL_GAS. Set Printing Coercions.
      Check ubor. Check boolOr.
      compute.
      admit.
    } all: admit.
  }
  clear P.  *)


  Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.
  rewrite Heqpre_suic in Heql'. compute in Heql'.
  Transparent xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.

  split. { rewrite Heql', eql. compute. reflexivity. }
  split. { rewrite Heql'. compute. reflexivity. }
  split. { rewrite Heql'. compute. reflexivity. }

  pose (stck := toValue (eval_state (sRReader IDefaultPtr_messages_right) l')).
  assert (stck = toValue (eval_state (sRReader IDefaultPtr_messages_right) l')) as E.
  reflexivity.
  rewrite <- E. rewrite Heql' in E.
  cbv beta iota delta -[stck xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush] in E.
  rewrite E. clear E stck.

  remember ((N.lor
  (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
     (uint2N DELETE_ME_IF_I_AM_EMPTY)) (uint2N IGNORE_ACTION_ERRORS))) as y.
  About SEND_ALL_GAS.
  compute in Heqy. subst y.

  (* apply messageSentTrivial. *)
Abort.



Lemma killBlank_noexec_proof : killBlank_noexec_prop eb address_to l.
Proof.
  unfold killBlank_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- killBlank_exec_prf in Heql'.
  unfold killBlank_exec in Heql'.
  intros Hnoreq. remember killBlank_isError_proof as prf. clear Heqprf.
  unfold killBlank_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- killBlank_err_prf in Hnoreq.
  unfold killBlank_err in Hnoreq.
  
  (* lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond
  end.

  unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
  unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'.
  all:cycle 1.
  unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'.
  subst l'. destruct l. repeat destruct p.
  destruct c. repeat destruct p. compute. reflexivity. *)

  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  destruct m. repeat destruct p.

  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l'; compute; repeat split; reflexivity
    ]
  end. discriminate Hnoreq.
Defined.


End killBlank.

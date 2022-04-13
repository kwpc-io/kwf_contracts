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

Section notifyRight.
Context (vbf :uint16) (eb: uint128) (giver : address ) (nonce : uint256)
(balance : uint128 ) (income : uint128) (l: LedgerLRecord ).

Definition notifyRight_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb)
    giver nonce balance income)) l)}.
  unfold UinterpreterL, notifyRight_, check_giver.
  repeat auto_build_P.
Defined.

Definition notifyRight_err : bool.
  term_of_2 notifyRight_err_P notifyRight_err_P.
Defined.

Definition notifyRight_err_prf : notifyRight_err =
  isError (eval_state (UinterpreterL (
    notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb)
    giver nonce balance income)) l).
  proof_of_2 notifyRight_err notifyRight_err_P notifyRight_err_P.
Defined.

Lemma notifyRight_isError_proof : notifyRight_isError_prop vbf eb giver nonce balance income l.
Proof.
  unfold notifyRight_isError_prop. rewrite isErrorEq.
  rewrite <- notifyRight_err_prf. unfold notifyRight_err.
  
  unfold notifyRight_requires.
  
  repeat (replace (exec_state _ _) with l; [|reflexivity]).

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
  - match goal with |- toValue (eval_state ?r0 ?l0) = false <-> _ =>
    replace (toValue (eval_state r0 l0)) with (toValue (eval_state r0 l)) end.
    2:{ destruct l. repeat destruct p.
      destruct v. repeat destruct p.
      reflexivity.
    }
    match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- toValue (eval_state ?r0 ?l0) = false <-> _ =>
    replace (toValue (eval_state r0 l0)) with (toValue (eval_state r0 l)) end.
    2:{ destruct l. repeat destruct p.
      destruct v. repeat destruct p.
      reflexivity.
    }
    match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N eb =>
      replace tv1 with (xIntGeb tv2 eb);
      [destruct tv2; destruct eb|reflexivity]
    end.
    simpl. rewrite N.leb_gt. reflexivity.
  - rewrite isErrorEq. match goal with |- _ <-> ?er = true => introduce er end.
    { unfold UinterpreterL, check_giver, new_lvalueL. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end; simpl; intuition.
Defined.

Definition notifyRight_exec_P :
  {t | t = exec_state (UinterpreterL (
    notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb)
    giver nonce balance income)) l}.
  unfold UinterpreterL, notifyRight_, check_giver.
  do 5 auto_build_P. 5:{ eexists; reflexivity. }
  all: repeat auto_build_P.
Defined.

Definition notifyRight_exec : LedgerLRecord.
  term_of_2 notifyRight_exec_P notifyRight_exec_P.
Defined.

Definition notifyRight_exec_prf : notifyRight_exec =
  exec_state (UinterpreterL (
    notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb)
    giver nonce balance income)) l.
  proof_of_2 notifyRight_exec notifyRight_exec_P notifyRight_exec_P.
Defined.

Definition notifyRight_unconditional_exec : LedgerLRecord.
  pose (l' := notifyRight_exec). unfold notifyRight_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.


Lemma notifyRight_remove_conditions_helper :
  forall {A1 A2 A3 A} (c1 c2 c3 : bool) (v1 : A1) (v2 : A2) (v3 : A3)
  (e1 e2 e3 : ErrorType) (a1 a2 a3 a : A),
  match (xBoolIfElse c1 (ControlValue true v1) (ControlError e1)) with
  | ControlValue _ _ =>
    match (xBoolIfElse c2 (ControlValue true v2) (ControlError e2)) with
    | ControlValue _ _ =>
      match (xBoolIfElse c3 (ControlValue true v3) (ControlError e3)) with
      | ControlValue _ _ => false
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
  a) = a.
Proof.
  intros.
  destruct c1. 2:{ exfalso. apply H. reflexivity. }
  destruct c2. 2:{ exfalso. apply H. reflexivity. }
  destruct c3. 2:{ exfalso. apply H. reflexivity. }
  simpl. reflexivity.
Defined.

Lemma notifyRight_remove_conditions : (~ (notifyRight_requires eb giver nonce l)) ->
  notifyRight_exec = notifyRight_unconditional_exec.
Proof.
  pose proof notifyRight_isError_proof as notifyRight_isError_proof'.
  pose proof notifyRight_err_prf as notifyRight_err_proof'.
  unfold notifyRight_err  in notifyRight_err_proof'.
  unfold notifyRight_isError_prop in  notifyRight_isError_proof'.
  rewrite isErrorEq in notifyRight_isError_proof'.

  intros Hnoreq. 
  rewrite <- notifyRight_isError_proof' in Hnoreq. clear notifyRight_isError_proof'.
  rewrite <- notifyRight_err_proof' in Hnoreq.

  clear notifyRight_err_proof'. unfold notifyRight_exec, notifyRight_unconditional_exec.

  apply (notifyRight_remove_conditions_helper _ _ _ _ _ _ _ _ _ _ _ _ _ Hnoreq).
Unshelve. all: let n := numgoals in guard n=0. Admitted.
(* Defined. *) (* long but checks *)

Lemma notifyRight_exec_proof : notifyRight_exec_prop vbf eb giver nonce balance income l.
Proof.
  (* destruct l eqn:E. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p. *)

  unfold notifyRight_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- notifyRight_exec_prf, notifyRight_remove_conditions in Heql'.
  2:{ assumption. } unfold notifyRight_unconditional_exec in Heql'.

  match goal with H : l' = exec_state _ ?ll |- _ => remember ll as l'' end.

  replace (uint2N (toValue (eval_state (sRReader || givers_summa_ ||) l)))
  with (uint2N (toValue (eval_state (sRReader || givers_summa_ ||) l''))).
  2:{ destruct l eqn:eql. repeat destruct p.
    destruct c. repeat destruct p.
    destruct v. repeat destruct p.
    subst l''. compute. reflexivity.
  }

  replace (toValue (eval_state (sRReader || int_sender () ||) l))
  with (toValue (eval_state (sRReader || int_sender () ||) l'')).
  2:{ destruct l eqn:eql. repeat destruct p.
    destruct c. repeat destruct p.
    destruct v. repeat destruct p.
    subst l''. compute. reflexivity.
  }

  clear Heql'' Hnoreq l. rename l'' into l.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3; try destruct l4;
    try destruct l5; try destruct l6; try destruct l7; try destruct l8; try destruct l9).
  destruct m. repeat destruct p. destruct m0. repeat destruct p.

  match goal with H : l' = ?t |- _ => introduce t end.
  {
    do 3 auto_build_P.
    {
      Unset Printing Notations. unfold tvm_transfer_left, wrapULExpression,
      SML_NG32.wrapULExpression. auto_build_P.
      unfold UExpressionP_Next_LedgerableWithRArgsL, UExpressionP_Next_LedgerableWithLArgsL,
      UExpressionP0_LedgerableWithArgsL, ursus_call_with_argsL.
      C_rrrr_exec_P.
      9:{
        unfold tvm_transfer. eexists. unshelve apply send_internal_message_exec_prf.
        - reflexivity.
        - reflexivity.
        - intros ? ? HH. match type of HH with ?t = _ => subst t end.
          reflexivity.
      }
      all: repeat auto_build_P.
    }
    all: repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq in Heql'. clear eq.
  remember (exec_state _ (exec_state (UinterpreterUnf {{tvm_accept ()}}) l)) as l_presend.
  unfold send_internal_message_exec in Heql'.
  replace  (exec_state (sRReader || int_sender () ||) l_presend) with l_presend in Heql'.
  2:{ reflexivity. }

  Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert.
  rewrite eql in Heql_presend. compute in Heql_presend.

  destruct vbf as [vbf0].
  repeat split.

  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0),
    (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: subst l' l_presend. 
    Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert. all: compute; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0),
    (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: subst l' l_presend l. 
    Transparent xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert.
    all: compute.
    all: destruct x3, income; reflexivity.
  - remember (exec_state _ l_presend) as l_sent.
    Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.
    rewrite Heql_presend in Heql_sent. compute in Heql_sent.
    Transparent xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.

    pose (addr := (toValue (eval_state (sRReader || int_sender () ||) l))).
    assert (addr = (toValue (eval_state (sRReader || int_sender () ||) l))) as eqaddr.
    { unfold addr. reflexivity. }
    rewrite <- eqaddr. rewrite eql in eqaddr. cbv beta iota delta -[addr] in eqaddr.
    rewrite eqaddr. clear eqaddr addr.

    match type of Heql' with _ = exec_state (rpureLWriterN _ ?t) _ =>
    remember t as balance_delta end.

    Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.
    rewrite Heql_sent in Heql'. compute in Heql'.

    pose (msgstck := toValue (eval_state (sRReader IDefaultPtr_messages_right) l')).
    assert (msgstck = toValue (eval_state (sRReader IDefaultPtr_messages_right) l')) as eqstck.
    { unfold msgstck. reflexivity. } rewrite <- eqstck.
    rewrite Heql' in eqstck. cbv beta iota delta -[msgstck] in eqstck.
    rewrite eqstck. clear eqstck msgstck.
    
    apply messageSentTrivial.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

Lemma notifyRight_noexec_proof : notifyRight_noexec_prop vbf eb giver nonce balance income l.
Proof.
  unfold notifyRight_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- notifyRight_exec_prf in Heql'.
  unfold notifyRight_exec in Heql'.
  intros Hnoreq. remember notifyRight_isError_proof as prf. clear Heqprf.
  unfold notifyRight_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- notifyRight_err_prf in Hnoreq.
  unfold notifyRight_err in Hnoreq.

  destruct l. repeat destruct p.
  destruct c. repeat destruct p.

  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l'; compute; split; reflexivity
    ]
  end. discriminate Hnoreq.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

End notifyRight.

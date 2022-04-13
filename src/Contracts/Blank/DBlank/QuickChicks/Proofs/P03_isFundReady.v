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


Section isFundReady.
Context (vbf :uint16) (pkin : uint256 ) (nonce : uint256) (l: LedgerLRecord ).

Definition isFundReady_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    isFundReady_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) pkin nonce)) l)}.
  unfold UinterpreterL, isFundReady_, check_investor, new_lvalueL.
  repeat auto_build_P.
Defined.

Definition isFundReady_err : bool.
  term_of_2 isFundReady_err_P isFundReady_err_P.
Defined.

Definition isFundReady_err_prf : isFundReady_err =
  isError (eval_state (UinterpreterL (
    isFundReady_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) pkin nonce)) l).
  proof_of_2 isFundReady_err isFundReady_err_P isFundReady_err_P.
Defined.

Lemma isFundReady_isError_proof : isFundReady_isError_prop vbf pkin nonce l.
Proof.
  unfold isFundReady_isError_prop. rewrite isErrorEq.
  rewrite <- isFundReady_err_prf. unfold isFundReady_err.
  unfold isFundReady_requires. rewrite isErrorEq.

  (* match goal with |- context [ exec_state (rpureLWriterN ?a ?b) ?l ] =>
  introduce (exec_state (rpureLWriterN a b) l) end.
  { repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq. clear eq. *)

  match goal with |- context [ isError ?err ] => introduce (isError err) end.
  { unfold UinterpreterL, check_investor, new_lvalueL. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq. clear eq.

  reflexivity.
Defined.

Definition isFundReady_exec_P :
  {t | t = exec_state (UinterpreterL (
    isFundReady_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) pkin nonce)) l}.
  unfold UinterpreterL, isFundReady_, check_investor.
  repeat auto_build_P.
Defined.

Definition isFundReady_exec : LedgerLRecord.
  term_of_2 isFundReady_exec_P isFundReady_exec_P.
Defined.

Definition isFundReady_exec_prf : isFundReady_exec =
  exec_state (UinterpreterL (
    isFundReady_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) pkin nonce)) l.
  proof_of_2 isFundReady_exec isFundReady_exec_P isFundReady_exec_P.
Defined.

Definition isFundReady_unconditional_exec : LedgerLRecord.
  pose (l' := isFundReady_exec). unfold isFundReady_exec in l'.
  match goal with l' := context [ exec_state (UinterpreterUnf ?e) ?a ] |- _ =>
  clear l'; exact (exec_state (UinterpreterUnf e) a) end.
Defined.

Lemma isFundReady_remove_conditions : (~ (isFundReady_requires vbf pkin nonce l)) ->
  isFundReady_exec = isFundReady_unconditional_exec.
Proof.
  pose proof isFundReady_isError_proof as isFundReady_isError_proof'.
  pose proof isFundReady_err_prf as isFundReady_err_proof'.
  unfold isFundReady_err  in isFundReady_err_proof'.
  unfold isFundReady_isError_prop in  isFundReady_isError_proof'.
  rewrite isErrorEq in isFundReady_isError_proof'.

  intros Hnoreq. 
  rewrite <- isFundReady_isError_proof' in Hnoreq. clear isFundReady_isError_proof'.
  rewrite <- isFundReady_err_proof' in Hnoreq.

  clear isFundReady_err_proof'. unfold isFundReady_exec.

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ => 
    destruct cond;
    [ unfold xBoolIfElse at 1 , CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1 , CommonInstances.boolFunRec at 1
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end. unfold isFundReady_unconditional_exec.
  reflexivity.
Admitted.

Lemma isFundReady_exec_proof : 
  (* match l with
  (_, (_, (_, _, (_, _, (_, _, (_, _, _, (_, _, (loc, loc_ind)), (loc'', loc_ind'', (loc', loc_ind')), _))))))%xprod =>
    loc = Datatypes.nil /\ loc_ind = Datatypes.nil /\
    loc' = Datatypes.nil /\ loc_ind' = Datatypes.nil /\
    loc'' = Datatypes.nil /\ loc_ind'' = Datatypes.nil
    end -> *)
    isFundReady_exec_prop vbf pkin nonce l.
Proof.
  unfold isFundReady_exec_prop. intros (*Hnil*) Hnoreq.
  remember (exec_state (UinterpreterL _) l) as l'.
  rewrite <- isFundReady_exec_prf, isFundReady_remove_conditions in Heql'.
  2:{ assumption. }

  unfold isFundReady_unconditional_exec in Heql'.
  match goal with H : l' = exec_state _ ?l'' |- _ => remember l'' as l_presend end.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3; try destruct l4;
    try destruct l5; try destruct l6; try destruct l7; try destruct l8; try destruct l9).
  destruct m. repeat destruct p. destruct m0. repeat destruct p.
  destruct o. repeat destruct p. destruct o0. repeat destruct p.

  (* destruct Hnil as [Hlheap [Hlheap_ind [Hlheap' [Hlheap_ind' [Hlheap'' Hlheap_ind''] ] ] ] ].
  rewrite Hlheap, Hlheap_ind, Hlheap', Hlheap_ind', Hlheap'', Hlheap_ind'' in eql. *)

  (* match goal with H : l' = ?t |- _ => introduce t end.
  { unfold send_internal_message_left, wrapULExpression, SML_NG32.wrapULExpression.
    auto_build_P. unfold ursus_call_with_argsL, UExpressionP_Next_LedgerableWithLArgsL,
    UExpressionP_Next_LedgerableWithRArgsL, UExpressionP0_LedgerableWithArgsL. C_lrr_exec_P.
    - exists l_presend. reflexivity.
    - exists l0. reflexivity.
    - exists l1. reflexivity.
    - remember (toValue (eval_state (sRReader || int_sender () ||) l)) as aaa.
      rewrite eql in Heqaaa. compute in Heqaaa. match goal with H : aaa = ?addr |- _ =>
      exists (ULIndex (URScalar addr) {{IKWFundParticipantPtr}}) end.
      rewrite Heql_presend, eql. admit.
      (* match goal with |- context [ finalize_ulvalue ?lv ] => exists lv end. reflexivity. *)
    - unfold default_with_sigmafield, eq_rect, right_or_false. simpl.
      unfold solution_left, eq_rect_r, eq_rect, eq_sym. eexists. reflexivity.
    - unfold ClassTypesNotations.IKWFundParticipant_Ф_notifyParticipant_right,
      eq_rect, right_or_false, urvalue_bind. auto_build_P.
      eexists. unfold eval_state. simpl.
      remember (LocalState001LProjEmbed _ _) as aaa.
      rewrite eql in Heqaaa. compute in Heqaaa. subst aaa.
      reflexivity.
    - eexists. unshelve apply send_internal_message_exec_prf.
      + match goal with |- _ (_ ?xx) _ = _ => subst xx end. reflexivity.
      + match goal with |- _ (_ ?xx) _ = _ => subst xx end. reflexivity.
      + intros xx l'' Hxx. subst xx.
        match goal with |- context [ finalize_ulvalue ?xx ] => subst xx end.
        reflexivity.
  } *)



  split. { rewrite Heql', Heql_presend.
    match goal with |- toValue (eval_state _ (exec_state _ (exec_state _ ?aa))) = false =>
    remember aa as aaa end.
    rewrite eql in Heqaaa. 
    (* compute in Heqaaa. subst aaa.  *)
    (* compute. *)
    (* remember (exec_state (rpureLWriterN (ULIndex _ _ ) _) _) as aaa.
    rewrite eql in Heqaaa. compute in Heqaaa. *)
  (* } *)

  (* unfold isFundReady_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) l) as l'.
  rewrite <- isFundReady_exec_prf in Heql'.
  unfold isFundReady_exec in Heql'.
  
  remember isFundReady_isError_proof as prf. clear Heqprf.
  unfold isFundReady_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf, <- isFundReady_err_prf in Hnoreq. clear prf.
  unfold isFundReady_err in Hnoreq.

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end. clear Hnoreq. *)
Abort.


End isFundReady.

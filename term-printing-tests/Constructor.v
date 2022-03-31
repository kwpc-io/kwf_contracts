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
Require Import UMLang.Args.ArgCorrectness.

Lemma isErrorEq : forall {R b} (cr : ControlResult R b),
  CommonQCEnvironment.isError cr <-> isError cr = true.
Proof. unfold isError, CommonQCEnvironment.isError. destruct cr; intuition. Defined.

Ltac leftmost_or t :=
  let rec tt := fun t =>
  match t with
  | ?A \/ _ => tt A
  | ?A => A
  end in tt constr:(t).

Lemma elim_left_absurd : forall P : Prop,
  true = false \/ P <-> P.
Proof.
  intros P. split; intros H.
  - destruct H as [H|H]. discriminate H. apply H.
  - right. apply H.
Defined.

Lemma messageSentTrivial : forall {A} `{XBoolEquable bool A}
  (msg : OutgoingMessage A)
  (msgMap : queue (OutgoingMessage A))
  (stateMap : mapping address (queue (OutgoingMessage A)))
  (ind : address),
  is_true (isMessageSent msg ind 0 (stateMap [ind] ← (hmapPush msg msgMap))).
Admitted.








Section finalize.
Context (eb: uint128) (gpm: uint128) (force_giveup :  XBool)
(addr: address) (l: LedgerLRecord )  .

Definition finalize_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb) (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l)}.
  unfold UinterpreterL, finalize_, check_owner.
  repeat auto_build_P.
Defined.

Definition finalize_err : bool.
  term_of_2 finalize_err_P finalize_err_P.
Defined.

Definition finalize_err_prf : finalize_err =
  isError (eval_state (UinterpreterL (
    finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb) (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l).
  proof_of_2 finalize_err finalize_err_P finalize_err_P.
Defined.

Lemma finalize_isError_proof : finalize_isError_prop eb gpm force_giveup addr l.
Proof.
  unfold finalize_isError_prop. rewrite isErrorEq.
  rewrite <- finalize_err_prf. unfold finalize_err.
  
  unfold finalize_requires.
  
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv3 tv2);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N eb + uint2N gpm =>
      replace tv1 with (xIntGeb tv2 (xIntPlus gpm eb));
      [destruct tv2; destruct eb; destruct gpm|reflexivity]
    end.
    simpl. rewrite N.leb_gt. lia.
  - lazymatch goal with |- ?tv1 = false <->
    uint2N ?tv2 < uint2N ?tv3 \/ uint2N ?tv4 > uint2N ?tv5 =>
    replace tv1 with (andb (xIntGeb tv2 tv3) (xIntLeb tv2 tv5));
    [destruct tv2; destruct tv3; destruct tv5|reflexivity]
    end.
    simpl. rewrite Bool.andb_false_iff. do 2 rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
      replace tv1 with (Common.eqb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. reflexivity.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
      replace tv1 with (boolNegb (Common.eqb tv2 (Build_XUBInteger 0)));
      [destruct tv2|reflexivity]
    end.
    simpl. destruct (N.eqb_spec x 0); split; intros; congruence.
Defined.

Definition finalize_exec_P :
  {t | t = exec_state (UinterpreterL (finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb)
  (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l}.
  unfold UinterpreterL, finalize_, check_owner.
  repeat auto_build_P.
Defined.

Definition finalize_exec : LedgerLRecord.
  term_of_2 finalize_exec_P finalize_exec_P.
Defined.

Definition finalize_exec_prf : finalize_exec =
  exec_state (UinterpreterL (finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb)
  (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l.
  proof_of_2 finalize_exec finalize_exec_P finalize_exec_P.
Defined.

Notation localcopy_state_lheap := (localcopy_state_lheap XUInteger XMaybe XProd).

Lemma finalize_exec_proof :
  match l with
    (_, (_, (_, _, (_, _, (_, _, (_, _, _, (loc, loc_ind, _), _, _))))))%xprod =>
    loc = Datatypes.nil /\ loc_ind = Datatypes.nil end ->
  finalize_exec_prop eb gpm force_giveup addr l.
Proof.
  intros Hnil.

  unfold finalize_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- finalize_exec_prf in Heql'.
  unfold finalize_exec in Heql'.

  remember finalize_isError_proof as prf. clear Heqprf.
  unfold finalize_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf, <- finalize_err_prf in Hnoreq. clear prf.
  unfold finalize_err in Hnoreq.

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end.
  
  match goal with H : l' = exec_state _ ?l'' |- _ => remember l'' as l_presend end.
  Unset Printing Notations. destruct addr.

  Opaque xHMapInsert hmapPush.
  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3; try destruct l4;
    try destruct l5; try destruct l6; try destruct l7; try destruct l8; try destruct l9).
  destruct m. repeat destruct p. destruct m0. repeat destruct p.
  destruct o. repeat destruct p. destruct o0. repeat destruct p.

  destruct Hnil as [Hlheap Hlheap_ind]. rewrite Hlheap, Hlheap_ind in eql.
  
  split. { subst l l' l_presend. compute. reflexivity. }
  split. { subst l l' l_presend. compute. reflexivity. }
  Transparent xHMapInsert hmapPush.
  match goal with H : l' = ?t |- _ => introduce t end.
  { unfold send_internal_message_left, wrapULExpression, SML_NG32.wrapULExpression.
    auto_build_P. unfold ursus_call_with_argsL, UExpressionP_Next_LedgerableWithLArgsL,
    UExpressionP_Next_LedgerableWithRArgsL, UExpressionP0_LedgerableWithArgsL. C_lrr_exec_P.
    - exists l_presend. reflexivity.
    - exists l0. reflexivity.
    - exists l1. reflexivity.
    - match goal with |- context [ finalize_ulvalue ?lv ] => exists lv end. reflexivity.
    - unfold default_with_sigmafield, eq_rect, right_or_false. simpl.
      unfold solution_left, eq_rect_r, eq_rect, eq_sym. eexists. reflexivity.
    - unfold ClassTypesNotations.IKWFundParticipant_Ф_notifyParticipant_right,
      eq_rect, right_or_false, urvalue_bind. auto_build_P.
      eexists. unfold eval_state. simpl.
      remember (LocalState010LProjEmbed _ _) as aaa.
      rewrite eql in Heqaaa. compute in Heqaaa. subst aaa.
      reflexivity.
    - eexists. unshelve apply send_internal_message_exec_prf.
      + match goal with |- _ (_ ?xx) _ = _ => subst xx end. reflexivity.
      + match goal with |- _ (_ ?xx) _ = _ => subst xx end. reflexivity.
      + intros xx l'' Hxx. subst xx.
        match goal with |- context [ finalize_ulvalue ?xx ] => subst xx end.
        reflexivity.
  }
  extract_eq as eq. rewrite <- eq in Heql'. clear eq.
  unfold send_internal_message_exec in Heql'.
  remember (exec_state _ l_presend) as l_msg.
  remember (OutgoingInternalMessage _ _) as msg.
  
  match goal with H : msg = OutgoingInternalMessage ?p ?v |- _ (_ (_ ?p' ?v') _ _ _) =>
  replace p with p' in Heqmsg; [|reflexivity];
  replace v with v' in Heqmsg end.
  2:{ simpl. unfold solution_left, eq_rect_r, eq_rect, eq_sym. f_equal.
    2:{ rewrite Heql_presend, eql. reflexivity. }
    2:{ rewrite Heql_presend, eql. reflexivity. }

    match goal with H : l_presend = exec_state (rpureLWriterN _ ?giveup_v) _ |- _ =>
    remember giveup_v as giveup_val end.
    match goal with H : giveup_val = toValue (eval_state ?c ?l') |- _ =>
    replace (toValue (eval_state c l')) with (toValue (eval_state c l)) in H end.
    2:{ rewrite eql. reflexivity. }

    lazymatch goal with |- ?c0 = _ =>
    replace c0 with giveup_val end.
    2:{ rewrite Heqgiveup_val. rewrite eql.
      Search "compare_cont".
      cbv beta iota zeta delta -[ ssrnat.nat_of_bin N.compare Nat.leb ].
      now destruct x5, x7, x8.
    }

    rewrite eql in Heqgiveup_val. compute in Heqgiveup_val.

    (* remember (toValue (eval_state (sRReader (ULtoRValue local_state_lheap)) l_presend))
    as heap_with_giveup.
    rewrite Heql_presend, eql in Heqheap_with_giveup.
    compute in Heqheap_with_giveup. *)

    (* match goal with H : context [ ("giveup"%string, ?ind)%core ] |- _ =>
    remember ind as next_index end. *)

    (* remember (LocalState001LProjEmbed _ _) as aaa.
    rewrite eql in Heqaaa. compute in Heqaaa. subst aaa.

    remember (LocalState001LProjEmbed _ _) as aaa.
    rewrite Heql_presend in Heqaaa. compute in Heqaaa.
    match goal with H : aaa = _ [("giveup"%string, next_index)] ← ?giveup_c |- _ =>
    remember giveup_c as giveup_cond end. subst aaa. *)

    rewrite Heql_presend, eql. compute. reflexivity.
  }
  rewrite <- Heqmsg. match goal with |- context [ toValue ?a ] =>
  remember (toValue a) as msg_stack end.

  remember (hmapPush msg _) as msg_added.
  match goal with H : msg_added = hmapPush _ ?msgM |- _ =>
  remember msgM as msgMap end.

  rewrite Heql', Heql_msg, Heql_presend, eql in Heqmsg_stack.
  compute in Heqmsg_stack. rewrite Heqmsg_stack.
  rewrite Heqmsg_added. apply messageSentTrivial.
Defined.

Lemma finalize_noexec_proof : finalize_noexec_prop eb gpm force_giveup addr l.
Proof.
  unfold finalize_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- finalize_exec_prf in Heql'.
  unfold finalize_exec in Heql'.
  intros Hnoreq. remember finalize_isError_proof as prf. clear Heqprf.
  unfold finalize_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- finalize_err_prf in Hnoreq.
  unfold finalize_err in Hnoreq.
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
Defined.

End finalize.

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

Definition leibniz_eqb {A} `{XBoolEquable bool A} :=
  forall (a b : A), Common.eqb a b = true <-> a = b.

Lemma messageSentTrivial : forall {A} `{inst : XBoolEquable bool A}
  (msg : OutgoingMessage A)
  (msgMap : queue (OutgoingMessage A))
  (stateMap : mapping address (queue (OutgoingMessage A)))
  (ind : address),
  @leibniz_eqb _ inst ->
  is_true (isMessageSent msg ind 0 (stateMap [ind] ← (hmapPush msg msgMap))).
Admitted.

Lemma insert_find : forall {K V} `{inst : XBoolEquable bool K} (spec : @leibniz_eqb _ inst)
  (vd v : V) (k : K) (li : CommonInstances.listPair K V),
  Common.hmapFindWithDefault vd k (xHMapInsert k v li) = v.
Admitted.















Section notifyLeft.
Context (vbf :uint16) (eb: uint128) (pkin : uint256 ) (nonce : uint256)
  (balance : uint128 ) (adj_balance : uint128) (l: LedgerLRecord ).

Definition notifyLeft_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l)}.
  unfold UinterpreterL, notifyLeft_, check_investor.
  repeat auto_build_P.
Defined.

Definition notifyLeft_err : bool.
  term_of_2 notifyLeft_err_P notifyLeft_err_P.
Defined.

Definition notifyLeft_err_prf : notifyLeft_err =
  isError (eval_state (UinterpreterL (
    notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l).
  proof_of_2 notifyLeft_err notifyLeft_err_P notifyLeft_err_P.
Defined.

Lemma notifyLeft_isError_proof : notifyLeft_isError_prop vbf eb pkin nonce balance adj_balance l.
Proof.
  unfold notifyLeft_isError_prop. rewrite isErrorEq.
  rewrite <- notifyLeft_err_prf. unfold notifyLeft_err.

  destruct l. clear l. repeat destruct p.
  destruct v. repeat destruct p.
  
  unfold notifyLeft_requires. rewrite isErrorEq.
  match goal with |- context [ isError ?err ] => introduce (isError err) end.
  { unfold  UinterpreterL, check_investor. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq. clear eq.
  
  (* repeat (replace (exec_state _ _) with l; [|reflexivity]). *)

  match goal with |- context [ (?a, ?b)%xprod ] =>
  set (l_orig := (a,b)%xprod) end.

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
  - remember (exec_state _ _) as l'.

    assert (toValue (eval_state (sRReader || tvm_now () ||) l_orig) =
      toValue (eval_state (sRReader || tvm_now () ||) l')) as eq_now.
    { subst l'. unfold l_orig. compute. reflexivity. }

    assert (toValue (eval_state (sRReader || lock_time_ ||) l_orig) =
      toValue (eval_state (sRReader || lock_time_ ||) l')) as eq_lock_time.
    { subst l'. compute. reflexivity. }

    unfold LedgerLRecord, LedgerL, ClassGenerator.prod_list in *.
    clear Heql'. unfold l_orig in eq_now. rewrite eq_now.
    unfold l_orig in eq_lock_time. rewrite eq_lock_time.
    clear eq_now eq_lock_time.

    match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - remember (exec_state _ _) as l'.
  
    assert (toValue (eval_state (sRReader || tvm_balance () ||) l_orig) =
      toValue (eval_state (sRReader || tvm_balance () ||) l')) as eq_balance.
    { subst l'. compute. reflexivity. }

    unfold LedgerLRecord, LedgerL, ClassGenerator.prod_list in *.
    unfold l_orig in eq_balance. rewrite eq_balance.
    clear Heql' eq_balance.

    match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N eb =>
      replace tv1 with (xIntGeb tv2 eb);
      [destruct tv2; destruct eb|reflexivity]
    end.
    simpl. rewrite N.leb_gt. reflexivity.
  - destruct (toValue _); simpl.
    + split; intros; discriminate.
    + split; reflexivity.
Defined.

Definition notifyLeft_exec_P :
  {t | t = exec_state (UinterpreterL (
    notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l}.
  unfold UinterpreterL, notifyLeft_. unfold check_investor. Check check_investor.
  repeat auto_build_P.
Defined.

Definition notifyLeft_exec : LedgerLRecord.
  term_of_2 notifyLeft_exec_P notifyLeft_exec_P.
Defined.

Definition notifyLeft_exec_prf : notifyLeft_exec =
  exec_state (UinterpreterL (
    notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l.
  proof_of_2 notifyLeft_exec notifyLeft_exec_P notifyLeft_exec_P.
Defined.

Definition notifyLeft_unconditional_exec : LedgerLRecord.
  pose (l' := notifyLeft_exec). unfold notifyLeft_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma notifyLeft_remove_conditions_helper :
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

Lemma notifyLeft_remove_conditions : (~ (notifyLeft_requires eb pkin nonce l)) ->
  notifyLeft_exec = notifyLeft_unconditional_exec.
Proof.
  pose proof notifyLeft_isError_proof as notifyLeft_isError_proof'.
  pose proof notifyLeft_err_prf as notifyLeft_err_proof'.
  unfold notifyLeft_err  in notifyLeft_err_proof'.
  unfold notifyLeft_isError_prop in  notifyLeft_isError_proof'.
  rewrite isErrorEq in notifyLeft_isError_proof'.

  intros Hnoreq. 
  rewrite <- notifyLeft_isError_proof' in Hnoreq. clear notifyLeft_isError_proof'.
  rewrite <- notifyLeft_err_proof' in Hnoreq.

  clear notifyLeft_err_proof'. unfold notifyLeft_exec, notifyLeft_unconditional_exec.

  apply (notifyLeft_remove_conditions_helper _ _ _ _ _ _ _ _ _ _ _ _ _ Hnoreq).
Admitted. (* long check, but checks *)

(* Lemma ueqb_exec_P_helper : forall {X} `{XBoolEquable boolean X}
  (r1 : URValue X false) (r2 : URValue X false) (l0 l1 l2 : LedgerLRecord),
  l1 = exec_state (sRReader r1) l0 ->
  l2 = exec_state (sRReader r2) l1 ->
  l2 = exec_state (sRReader (ueqb r1 r2)) l0.
Proof.
  intros. unfold ueqb, eq_rect, right_or_false,
  urvalue_bindL, urvalue_bind, exec_state. simpl.

  replace (simple_state_run (sRReader r1) l0)
  with (eval_state (sRReader r1) l0, exec_state (sRReader r1) l0)%xprod.
  2:{ unfold exec_state, eval_state. simpl. destruct (simple_state_run _ _). reflexivity. }
  rewrite <- H0. remember (eval_state _ _) as c0. dependent destruction c0. simpl.

  replace (simple_state_run (sRReader r2) l1)
  with (eval_state (sRReader r2) l1, exec_state (sRReader r2) l1)%xprod.
  2:{ unfold exec_state, eval_state. simpl. destruct (simple_state_run _ _). reflexivity. }
  rewrite <- H1. remember (eval_state _ l1) as c1. dependent destruction c1. simpl.

  reflexivity.
Defined.

Ltac ueqb_exec_P := lazymatch goal with
  |- {t | t = exec_state (sRReader (ueqb ?r1 ?r2)) ?l0} =>
  match simpl_last_type_arg r1 with false =>
  match simpl_last_type_arg r2 with false =>
  assert {t | t = exec_state (sRReader r1) l0} as [l1?]; [|
  assert {t | t = exec_state (sRReader r2) l1} as [l2 ?]; [|
  exists l2; apply (ueqb_exec_P_helper r1 r2 l0 l1 l2); assumption
  ] ]
  end end end.

Goal forall {X} `{XBoolEquable boolean X}
  (r1 : URValue X false) (r2 : URValue X false) (l0 : LedgerLRecord),
  {t | t = exec_state (sRReader (ueqb r1 r2)) l0}.
  intros. ueqb_exec_P.
Abort. *)


(* Lemma readerq_check_equiv : forall l', l' = exec_state (Uinterpreter (
  check_investor pkin nonce _ _ {{ return_ #{PhantomPoint} }})) l ->
  ~ notifyLeft_requires eb pkin nonce l ->
  uint2N (toValue (eval_state (sRReader || investors_adj_summa_ ||) l')) =
  uint2N (toValue (eval_state (sRReader || investors_adj_summa_ ||) l)) /\
  uint2N (toValue (eval_state (sRReader || investors_summa_ ||) l')) =
  uint2N (toValue (eval_state (sRReader || investors_summa_ ||) l)) /\
  uint2N (toValue (eval_state (sRReader || num_investors_sent_ ||) l')) =
  uint2N (toValue (eval_state (sRReader || num_investors_sent_ ||) l)).
Proof.
  intros l' H Hnoreq. match goal with H : l' = ?t |- _ => introduce t end.
  { unfold check_investor. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq in H. clear eq.
  
  unfold notifyLeft_requires in Hnoreq.
  rewrite isErrorEq in Hnoreq. match goal with Hnoreq : ~ (?t = true \/ _) |- _ =>
  introduce t end.
  { unfold check_investor, UinterpreterL. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq in Hnoreq. clear eq.

  match goal with H : l' = (if xBoolIfElse ?c _ _ then _ else _) |- _ =>
  destruct c end. 2:{ simpl in Hnoreq. exfalso. apply Hnoreq. left. reflexivity. }
  unfold xBoolIfElse, CommonInstances.boolFunRec in H.

  clear Hnoreq.

  match goal with H : l' = exec_state _ (exec_state _ ?t) |- _ => introduce t end.
  { Unset Printing Notations. unfold tvm_msg_sender, wrapURValueL, addr_std_ι_address_right.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq in H. clear eq.

  match goal with H : l' = exec_state _ ?t |- _ => introduce t end.
  { auto_build_P. auto_build_P. auto_build_P. unfold local_state_lheap. auto_build_P.
    unfold local_state_lheap. auto_build_P.
  }
  extract_eq as eq. rewrite <- eq in H. clear eq.

  match goal with H : l' = ?t |- _ => introduce t end.
  { 
    (* match goal with |- {t | t = exec_state _ ?tt} => exists tt;
    remember tt eqn:eq; clear eq end. *)
    Unset Printing Notations. unfold wrapURValueL,
    SML_NG32.wrapURValue. ueqb_exec_P.
    Unset Printing Notations. unfold ULtoRValueL.
    auto_build_P. unfold local_state_lheap. auto_build_P.
    auto_build_P. auto_build_P. auto_build_P.
    unfold getKWDPoolAddress_right. unfold wrapURExpression, SML_NG32.wrapURExpression.
    auto_build_P.
    unfold UExpressionP_Next_LedgerableWithRArgsL, UExpressionP_Next_LedgerableWithLArgsL,
    UExpressionP0_LedgerableWithArgsL, ursus_call_with_argsL.
    C_rr_exec_P.
    auto_build_P. auto_build_P. auto_build_P. auto_build_P. unfold getKWDPoolAddress_.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq in H. clear eq.


  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p. subst l'. compute.
  repeat split; reflexivity.
Defined. *)

(* Lemma notifyLeft_exec_nocompute_proof : notifyLeft_exec_prop vbf eb pkin nonce balance adj_balance l.
Proof.
  unfold notifyLeft_exec_prop. remember (exec_state _ l) as l'.
  intros Hnoreq. rewrite <- notifyLeft_exec_prf,
  notifyLeft_remove_conditions in Heql'. 2:{ assumption. }
  unfold notifyLeft_unconditional_exec in Heql'.

  remember (exec_state (sRReader || !{_} == {_} ||) _) as l''.

  Set Printing Implicit.

  unshelve epose proof (readerq_check_equiv l'' _) as [eq1 ].
  { rewrite Heql''. unfold XList. reflexivity. assumption. }

  match goal with H : l'' = exec_state _ (exec_state _ ?t) |- _ =>
  introduce t end.
  { Unset Printing Notations. unfold wrapURValueL, tvm_msg_sender,
    addr_std_ι_address_right. repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq in Heql''. clear eq.

  match goal with H : l'' = exec_state _ ?t |- _ =>
  introduce t end.
  { auto_build_P. auto_build_P. auto_build_P. unfold local_state_lheap.
    auto_build_P. unfold local_state_lheap. auto_build_P.
  }
  extract_eq as eq. rewrite <- eq in Heql''. clear eq.

  match goal with H : l'' = ?t |- _ =>
  introduce t end.
  { unfold getKWDPoolAddress_right.
    
    match goal with |- {t | t = exec_state _ ?tt} => exists tt end.
    
  }
  extract_eq as eq. rewrite <- eq in Heql''. clear eq.


  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.

  replace (toValue (eval_state (sRReader || investors_adj_summa_ ||) l))
  with (toValue (eval_state (sRReader || investors_adj_summa_ ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  replace (toValue (eval_state (sRReader || investors_summa_ ||) l))
  with (toValue (eval_state (sRReader || investors_summa_ ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  replace (toValue (eval_state (sRReader || num_investors_sent_ ||) l))
  with (toValue (eval_state (sRReader || num_investors_sent_ ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  replace (toValue (eval_state (sRReader || int_sender () ||) l))
  with (toValue (eval_state (sRReader || int_sender () ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  clear Heql'' eql Hnoreq l. rename l'' into l.

  repeat match goal with H : uint8 |- _ => clear H end.
  repeat match goal with H : uint16 |- _ => clear H end.
  repeat match goal with H : uint32 |- _ => clear H end.
  repeat match goal with H : uint128 |- _ => clear H end.
  repeat match goal with H : uint256 |- _ => clear H end.
  repeat match goal with H : boolean |- _ => clear H end.
  repeat match goal with H : cell_ |- _ => clear H end.
  clear x23 c0 m m0 a a0 l0 l1.

  match goal with H : l' = exec_state _ ?ll |- _ =>
  remember ll as l_pretransfer end.

  match goal with H : l' = ?t |- _ => introduce t end.
  {
    Unset Printing Notations.
    unfold tvm_transfer_left, wrapULExpression, SML_NG32.wrapULExpression, wrapURValueL.
    auto_build_P. unfold ursus_call_with_argsL, UExpressionP_Next_LedgerableWithLArgsL,
    UExpressionP_Next_LedgerableWithRArgsL, UExpressionP0_LedgerableWithArgsL. C_rrrr_exec_P.
    - exists l_pretransfer. reflexivity.
    - exists l0. reflexivity.
    - exists l1. reflexivity.
    - exists l2. reflexivity.
    - unfold tvm_msg_sender. do 2 auto_build_P.
    - exists (Build_XUBInteger 0). reflexivity.
    - auto_build_P.
    - do 3 auto_build_P.
    - unfold tvm_transfer. eexists. unshelve apply send_internal_message_exec_prf.
      + reflexivity. 
      + reflexivity.
      + intros x0' l0' Hx0'. subst x0'. reflexivity.
  }
  extract_eq as eq. rewrite <- eq in Heql'. clear eq. unfold send_internal_message_exec in Heql'.
  remember (hmapPush _ _) as msg_state_sent.
  remember (exec_state _ l_pretransfer) as l_sent.
  remember (toValue (eval_state _ l_pretransfer)) as present_stack.

  unfold _defaultMessageQueue, IDefaultPtr_messages_left in *.

  match goal with H : l_sent = ?t |- _ => introduce t end.
  { repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq in Heql_sent. clear eq.

  match goal with H : present_stack = ?t |- _ => introduce t end.
  { repeat auto_build_P. unfold ULtoRValue, ULValueP_rect. auto_build_P. }
  extract_eq as eq. rewrite <- eq in Heqpresent_stack. clear eq.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3;
  try destruct l4; try destruct l5; try destruct l6; try destruct l7;
  try destruct l8; try destruct l9).
  destruct c0. repeat destruct p.
  destruct m. repeat destruct p.
  destruct g. repeat destruct p.
  destruct o. repeat destruct p.
  destruct m0. repeat destruct p.
  destruct g. repeat destruct p.
  destruct o. repeat destruct p.

  rewrite eql in Heql_pretransfer. Opaque xIntPlus xIntMinus. compute in Heql_pretransfer.
  Opaque Common.hmapFindWithDefault.
  rewrite Heql_pretransfer in Heqpresent_stack. compute in Heqpresent_stack.
  (* rewrite Heql_pretransfer in Heqpresent_stack. *)
  (* compute in Heqpresent_stack. *)
  (* subst present_stack. *)

  rewrite Heql_pretransfer in Heql_sent.
  Opaque xHMapInsert.
  compute in Heql_sent.

  destruct vbf as [vbf0].
  destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0) eqn:E1;
  destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0) eqn:E2.
  
  all: rewrite Heql_sent in Heql'; compute in Heql'.
  all:cycle 1.
  all:cycle 1.
  all:cycle 1.
  repeat split.
  - rewrite Heql', Heql_sent. reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: match goal with |- ?a = _ => remember a as aaa end;
    rewrite Heql' in Heqaaa; compute in Heqaaa.
    all: rewrite eql; compute; rewrite Heqaaa.
    all: destruct x4, adj_balance; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: match goal with |- ?a = _ => remember a as aaa end;
    rewrite Heql' in Heqaaa; compute in Heqaaa.
    all: rewrite eql; compute; rewrite Heqaaa.
    all: destruct x5, balance; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: match goal with |- ?a = _ => remember a as aaa end;
    rewrite Heql' in Heqaaa; compute in Heqaaa.
    all: rewrite eql; compute; rewrite Heqaaa.
    all: destruct x14; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0) eqn:E1;
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0) eqn:E2.
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: remember (toValue (eval_state (sRReader IDefaultPtr_messages_right) l'))
    as msg_stack; rewrite Heql' in Heqmsg_stack; compute in Heqmsg_stack.
    all: assert (exists addr, addr = toValue (eval_state (sRReader || int_sender () ||) l))
    as [addr Heqaddr]; [eexists; reflexivity|]; rewrite <- Heqaddr;
    rewrite eql in Heqaddr; compute in Heqaddr; rewrite Heqaddr; clear Heqaddr addr.
  
    all: rewrite Heqmsg_stack, Heqmsg_state_sent;
    apply messageSentTrivial.
Defined. *)

Definition notifyLeft_explicit_exec :=
  let l' := exec_state (Uinterpreter (
    check_investor pkin nonce _ _ {{ return_ #{PhantomPoint} }})) l in
  match vbf with Build_XUBInteger vbf0 =>
  match l' with ((x,
  (x0,
  (x1,
  (x2,
  (x3,
  (x4,
  (x5,
  (x6,
  (x7,
  (x8,
  (x9,
  (x10,
  (x11,
  (x12,
  (x13,
  (x14,
  (x15,
  (x16,
  (x17, (x18, (x19, (x20, (x21, (x22, (x23, (x24, (x25, x26)))))))))))))))))))))))))))%core,
 ((x64,
  (x65,
  (x66,
  (x67,
  (x68,
  (x69,
  (x70,
  (x71,
  (x72,
  (x73,
  (x74,
  (x75,
  (x76,
  (x77,
  (x78,
  (x79,
  (x80,
  (x81,
  (x82, (x83, (x84, (x85, (x86, (x87, (x88, (x89, (x90, x91)))))))))))))))))))))))))))%core,
    (x92,
    (x93,
    (x94,
    (x95,
    (x96,
    (x97,
    ((x99, (x100, (x101, x102)))%core, ((a1, (x103, x104))%core, x98))))))),
    (x105,
    (x106,
    (x107,
    (x108,
    (x109,
    (x110,
    ((x112, (x113, (x114, x115)))%core, ((a2, (x116, x117))%core, x111))))))),
    (x27,
    (x28,
    (x29,
    (a, (x30, (x31, (a0, (c, (c1, (x32, (x33, (c2, (x34, x35)))))))))))),
    (x60, x61, (x56, x57), (x52, x53, (x44, x45)),
    (x48, x49, (x40, x41), (x36, x37)),
    (x62, x63, (x58, x59), (x54, x55, (x46, x47)),
    (x50, x51, (x42, x43), (x38, x39)))))))))%xprod =>
      let present_stack := Common.hmapFindWithDefault Datatypes.nil a x92 in
      let msg_state_sent := hmapPush
        (EmptyMessage PhantomType (Build_XUBInteger 0, (xBoolFalse, vbf)))
        present_stack in
      if Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0 : bool
      then if Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0 : bool
        then ((x,
        (x0,
        (x1,
        (x2,
        (x3,
        (xIntPlus x4 adj_balance,
        (xIntPlus x5 balance,
        (x6,
        (x7,
        (x8,
        (x9,
        (x10,
        (x11,
        (x12,
        (x13,
        (xIntPlus x14 (Build_XUBInteger 1),
        (x15,
        (x16,
        (x17, (x18, (x19, (x20, (x21, (x22, (x23, (x24, (x25, x26)))))))))))))))))))))))))))%core,
       ((x64,
        (x65,
        (x66,
        (x67,
        (x68,
        (x69,
        (x70,
        (x71,
        (x72,
        (x73,
        (x74,
        (x75,
        (x76,
        (x77,
        (x78,
        (x79,
        (x80,
        (x81,
        (x82, (x83, (x84, (x85, (x86, (x87, (x88, (x89, (x90, x91)))))))))))))))))))))))))))%core,
       (x92 [a]← msg_state_sent,
       (x93,
       (x94,
       (x95,
       (x96,
       (x97,
       ((x99, (x100, (x101, x102)))%core, ((a1, (x103, x104))%core, x98))))))),
       (x105,
       (x106,
       (x107,
       (x108,
       (x109,
       (x110,
       ((x112, (x113, (x114, x115)))%core, ((a2, (x116, x117))%core, x111))))))),
       (x27,
       (x28,
       (x29,
       (a,
       (x30,
       (xIntMinus x31 (Build_XUBInteger 0),
       (a0, (c, (c1, (true, (x33, (c2, (x34, x35)))))))))))),
       (x60, x61, (x56, x57), (x52, x53, (x44, x45)),
       (x48, x49, (x40, x41), (x36, x37)),
       (x62, x63, (x58, x59), (x54, x55, (x46, x47)),
       (x50, x51, (x42, x43), (x38, x39)))))))))%xprod
        else ((x,
        (x0,
        (x1,
        (x2,
        (x3,
        (xIntPlus x4 adj_balance,
        (xIntPlus x5 balance,
        (x6,
        (x7,
        (x8,
        (x9,
        (x10,
        (x11,
        (x12,
        (x13,
        (xIntPlus x14 (Build_XUBInteger 1),
        (x15,
        (x16,
        (x17, (x18, (x19, (x20, (x21, (x22, (x23, (x24, (x25, x26)))))))))))))))))))))))))))%core,
       ((x64,
        (x65,
        (x66,
        (x67,
        (x68,
        (x69,
        (x70,
        (x71,
        (x72,
        (x73,
        (x74,
        (x75,
        (x76,
        (x77,
        (x78,
        (x79,
        (x80,
        (x81,
        (x82, (x83, (x84, (x85, (x86, (x87, (x88, (x89, (x90, x91)))))))))))))))))))))))))))%core,
       (x92 [a]← msg_state_sent,
       (x93,
       (x94,
       (x95,
       (x96,
       (x97,
       ((x99, (x100, (x101, x102)))%core, ((a1, (x103, x104))%core, x98))))))),
       (x105,
       (x106,
       (x107,
       (x108,
       (x109,
       (x110,
       ((x112, (x113, (x114, x115)))%core, ((a2, (x116, x117))%core, x111))))))),
       (x27,
       (x28,
       (x29,
       (a,
       (x30,
       (xIntMinus x31 (xIntMinus x31 x33),
       (a0, (c, (c1, (true, (x33, (c2, (x34, x35)))))))))))),
       (x60, x61, (x56, x57), (x52, x53, (x44, x45)),
       (x48, x49, (x40, x41), (x36, x37)),
       (x62, x63, (x58, x59), (x54, x55, (x46, x47)),
       (x50, x51, (x42, x43), (x38, x39)))))))))%xprod
      else if Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0 : bool
        then ((x,
        (x0,
        (x1,
        (x2,
        (x3,
        (xIntPlus x4 adj_balance,
        (xIntPlus x5 balance,
        (x6,
        (x7,
        (x8,
        (x9,
        (x10,
        (x11,
        (x12,
        (x13,
        (xIntPlus x14 (Build_XUBInteger 1),
        (x15,
        (x16,
        (x17, (x18, (x19, (x20, (x21, (x22, (x23, (x24, (x25, x26)))))))))))))))))))))))))))%core,
       ((x64,
        (x65,
        (x66,
        (x67,
        (x68,
        (x69,
        (x70,
        (x71,
        (x72,
        (x73,
        (x74,
        (x75,
        (x76,
        (x77,
        (x78,
        (x79,
        (x80,
        (x81,
        (x82, (x83, (x84, (x85, (x86, (x87, (x88, (x89, (x90, x91)))))))))))))))))))))))))))%core,
       (x92 [a]← msg_state_sent,
       (x93,
       (x94,
       (x95,
       (x96,
       (x97,
       ((x99, (x100, (x101, x102)))%core, ((a1, (x103, x104))%core, x98))))))),
       (x105,
       (x106,
       (x107,
       (x108,
       (x109,
       (x110,
       ((x112, (x113, (x114, x115)))%core, ((a2, (x116, x117))%core, x111))))))),
       (x27,
       (x28,
       (x29,
       (a,
       (x30,
       (xIntMinus x31 (xIntMinus x30 x33),
       (a0, (c, (c1, (true, (x33, (c2, (x34, x35)))))))))))),
       (x60, x61, (x56, x57), (x52, x53, (x44, x45)),
       (x48, x49, (x40, x41), (x36, x37)),
       (x62, x63, (x58, x59), (x54, x55, (x46, x47)),
       (x50, x51, (x42, x43), (x38, x39)))))))))%xprod
        else ((x,
        (x0,
        (x1,
        (x2,
        (x3,
        (xIntPlus x4 adj_balance,
        (xIntPlus x5 balance,
        (x6,
        (x7,
        (x8,
        (x9,
        (x10,
        (x11,
        (x12,
        (x13,
        (xIntPlus x14 (Build_XUBInteger 1),
        (x15,
        (x16,
        (x17, (x18, (x19, (x20, (x21, (x22, (x23, (x24, (x25, x26)))))))))))))))))))))))))))%core,
       ((x64,
        (x65,
        (x66,
        (x67,
        (x68,
        (x69,
        (x70,
        (x71,
        (x72,
        (x73,
        (x74,
        (x75,
        (x76,
        (x77,
        (x78,
        (x79,
        (x80,
        (x81,
        (x82, (x83, (x84, (x85, (x86, (x87, (x88, (x89, (x90, x91)))))))))))))))))))))))))))%core,
       (x92 [a]← msg_state_sent,
       (x93,
       (x94,
       (x95,
       (x96,
       (x97,
       ((x99, (x100, (x101, x102)))%core, ((a1, (x103, x104))%core, x98))))))),
       (x105,
       (x106,
       (x107,
       (x108,
       (x109,
       (x110,
       ((x112, (x113, (x114, x115)))%core, ((a2, (x116, x117))%core, x111))))))),
       (x27,
       (x28,
       (x29,
       (a,
       (x30,
       (xIntMinus x31 (xIntMinus x31 x33),
       (a0, (c, (c1, (true, (x33, (c2, (x34, x35)))))))))))),
       (x60, x61, (x56, x57), (x52, x53, (x44, x45)),
       (x48, x49, (x40, x41), (x36, x37)),
       (x62, x63, (x58, x59), (x54, x55, (x46, x47)),
       (x50, x51, (x42, x43), (x38, x39)))))))))%xprod
  end
end.

Lemma notifyLeft_explicit_exec_proof : ~ notifyLeft_requires eb pkin nonce l ->
  notifyLeft_unconditional_exec = notifyLeft_explicit_exec.
Proof.
  intros Hnoreq.
  unfold notifyLeft_unconditional_exec, notifyLeft_explicit_exec.
  remember (exec_state (sRReader || !{_} == {_} ||) _) as l''.
  remember (exec_state
  (Uinterpreter
     (check_investor pkin nonce PhantomType false
        {{(return_ #{PhantomPoint} )}})) l) as l0''.
  assert (l0'' = l'') as eq.
  {
    subst l0'' l''. unfold check_investor.
    match goal with |- ?t = _ => introduce t end.
    { repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    unfold notifyLeft_requires in Hnoreq.
    rewrite isErrorEq in Hnoreq.
    introduce (isError
    (eval_state
       (UinterpreterL
          (check_investor pkin nonce PhantomType false
             {{(return_ #{PhantomPoint})}})) l)).
    { unfold UinterpreterL, check_investor. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq in Hnoreq. clear eq.
    match goal with |- (if xBoolIfElse ?c _ _ then _ else _) = _ =>
    destruct c end.
    2:{ simpl in Hnoreq. exfalso. apply Hnoreq. left. reflexivity. }
    clear Hnoreq. unfold xBoolIfElse, CommonInstances.boolFunRec at 1.
    reflexivity.
  }
  rewrite eq. clear eq Heql0'' l0'' Heql'' Hnoreq l. rename l'' into l.
  Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert.

  match goal with |- ?t = _ => remember t as l' end.
  match goal with H : l' = exec_state _ ?ll |- _ =>
  remember ll as l_pretransfer end.

  match goal with H : l' = ?t |- _ => introduce t end.
  {
    Unset Printing Notations.
    unfold tvm_transfer_left, wrapULExpression, SML_NG32.wrapULExpression, wrapURValueL.
    auto_build_P. unfold ursus_call_with_argsL, UExpressionP_Next_LedgerableWithLArgsL,
    UExpressionP_Next_LedgerableWithRArgsL, UExpressionP0_LedgerableWithArgsL. C_rrrr_exec_P.
    - exists l_pretransfer. reflexivity.
    - exists l0. reflexivity.
    - exists l1. reflexivity.
    - exists l2. reflexivity.
    - unfold tvm_msg_sender. do 2 auto_build_P.
    - exists (Build_XUBInteger 0). reflexivity.
    - auto_build_P.
    - do 3 auto_build_P.
    - unfold tvm_transfer. eexists. unshelve apply send_internal_message_exec_prf.
      + reflexivity. 
      + reflexivity.
      + intros x0' l0' Hx0'. subst x0'. reflexivity.
  }
  extract_eq as eq. rewrite <- eq in Heql'. clear eq. unfold send_internal_message_exec in Heql'.
  remember (hmapPush _ _) as msg_state_sent.
  remember (exec_state _ l_pretransfer) as l_sent.
  remember (toValue (eval_state _ l_pretransfer)) as present_stack.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3;
  try destruct l4; try destruct l5; try destruct l6; try destruct l7;
  try destruct l8; try destruct l9).
  destruct c0. repeat destruct p.
  destruct m. repeat destruct p.
  destruct g. repeat destruct p.
  destruct o. repeat destruct p.
  destruct m0. repeat destruct p.
  destruct g. repeat destruct p.
  destruct o. repeat destruct p.

  rewrite eql in Heql_pretransfer. compute in Heql_pretransfer.
  rewrite Heql_pretransfer in Heqpresent_stack. compute in Heqpresent_stack.

  rewrite Heql_pretransfer in Heql_sent.
  compute in Heql_sent.

  destruct vbf as [vbf0].
  destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
  destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).

  all: rewrite Heql_sent in Heql'; compute in Heql'.
  all: rewrite Heqmsg_state_sent, Heqpresent_stack in Heql'.
  all: apply Heql'.
Abort.

Lemma notifyLeft_exec_proof : notifyLeft_exec_prop vbf eb pkin nonce balance adj_balance l.
Proof.
  unfold notifyLeft_exec_prop. remember (exec_state _ l) as l'.
  intros Hnoreq. rewrite <- notifyLeft_exec_prf,
  notifyLeft_remove_conditions in Heql'. 2:{ assumption. }
  unfold notifyLeft_unconditional_exec in Heql'.

  remember (exec_state (sRReader || !{_} == {_} ||) _) as l''.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.

  replace (toValue (eval_state (sRReader || investors_adj_summa_ ||) l))
  with (toValue (eval_state (sRReader || investors_adj_summa_ ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  replace (toValue (eval_state (sRReader || investors_summa_ ||) l))
  with (toValue (eval_state (sRReader || investors_summa_ ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  replace (toValue (eval_state (sRReader || num_investors_sent_ ||) l))
  with (toValue (eval_state (sRReader || num_investors_sent_ ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  replace (toValue (eval_state (sRReader || int_sender () ||) l))
  with (toValue (eval_state (sRReader || int_sender () ||) l'')).
  2:{ rewrite Heql'', eql. reflexivity. }

  clear Heql'' eql Hnoreq l. rename l'' into l.

  repeat match goal with H : uint8 |- _ => clear H end.
  repeat match goal with H : uint16 |- _ => clear H end.
  repeat match goal with H : uint32 |- _ => clear H end.
  repeat match goal with H : uint128 |- _ => clear H end.
  repeat match goal with H : uint256 |- _ => clear H end.
  repeat match goal with H : boolean |- _ => clear H end.
  repeat match goal with H : cell_ |- _ => clear H end.
  clear x23 c0 m m0 a a0 l0 l1.

  match goal with H : l' = exec_state _ ?ll |- _ =>
  remember ll as l_pretransfer end.

  match goal with H : l' = ?t |- _ => introduce t end.
  {
    Unset Printing Notations.
    unfold tvm_transfer_left, wrapULExpression, SML_NG32.wrapULExpression, wrapURValueL.
    auto_build_P. unfold ursus_call_with_argsL, UExpressionP_Next_LedgerableWithLArgsL,
    UExpressionP_Next_LedgerableWithRArgsL, UExpressionP0_LedgerableWithArgsL. C_rrrr_exec_P.
    - exists l_pretransfer. reflexivity.
    - exists l0. reflexivity.
    - exists l1. reflexivity.
    - exists l2. reflexivity.
    - unfold tvm_msg_sender. do 2 auto_build_P.
    - exists (Build_XUBInteger 0). reflexivity.
    - auto_build_P.
    - do 3 auto_build_P.
    - unfold tvm_transfer. eexists. unshelve apply send_internal_message_exec_prf.
      + reflexivity. 
      + reflexivity.
      + intros x0' l0' Hx0'. subst x0'. reflexivity.
  }
  extract_eq as eq. rewrite <- eq in Heql'. clear eq. unfold send_internal_message_exec in Heql'.
  remember (hmapPush _ _) as msg_state_sent.
  remember (exec_state _ l_pretransfer) as l_sent.
  remember (toValue (eval_state _ l_pretransfer)) as present_stack.

  unfold _defaultMessageQueue, IDefaultPtr_messages_left in *.

  match goal with H : l_sent = ?t |- _ => introduce t end.
  { repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq in Heql_sent. clear eq.

  match goal with H : present_stack = ?t |- _ => introduce t end.
  { repeat auto_build_P. unfold ULtoRValue, ULValueP_rect. auto_build_P. }
  extract_eq as eq. rewrite <- eq in Heqpresent_stack. clear eq.
  Check @hmapFindWithDefault. 

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3;
  try destruct l4; try destruct l5; try destruct l6; try destruct l7;
  try destruct l8; try destruct l9).
  destruct c0. repeat destruct p.
  destruct m. repeat destruct p.
  destruct g. repeat destruct p.
  destruct o. repeat destruct p.
  destruct m0. repeat destruct p.
  destruct g. repeat destruct p.
  destruct o. repeat destruct p.

  rewrite eql in Heql_pretransfer. Opaque xIntPlus xIntMinus. compute in Heql_pretransfer.
  Opaque Common.hmapFindWithDefault.
  rewrite Heql_pretransfer in Heqpresent_stack. compute in Heqpresent_stack.
  (* rewrite Heql_pretransfer in Heqpresent_stack. *)
  (* compute in Heqpresent_stack. *)
  (* subst present_stack. *)

  rewrite Heql_pretransfer in Heql_sent.
  Opaque xHMapInsert.
  compute in Heql_sent.

  destruct vbf as [vbf0].
  (* destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0) eqn:E1;
  destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0) eqn:E2.
  
  all: rewrite Heql_sent in Heql'; compute in Heql'. *)
  repeat split.
  - rewrite Heql', Heql_sent. reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: match goal with |- ?a = _ => remember a as aaa end;
    rewrite Heql' in Heqaaa; compute in Heqaaa.
    all: rewrite eql; compute; rewrite Heqaaa.
    all: destruct x4, adj_balance; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: match goal with |- ?a = _ => remember a as aaa end;
    rewrite Heql' in Heqaaa; compute in Heqaaa.
    all: rewrite eql; compute; rewrite Heqaaa.
    all: destruct x5, balance; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0);
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0).
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: match goal with |- ?a = _ => remember a as aaa end;
    rewrite Heql' in Heqaaa; compute in Heqaaa.
    all: rewrite eql; compute; rewrite Heqaaa.
    all: destruct x14; reflexivity.
  - destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N MSG_VALUE_BUT_FEE)) 0) eqn:E1;
    destruct (Common.eqb (N.land vbf0 (tvmFunc.uint2N SEND_ALL_GAS)) 0) eqn:E2.
    all: rewrite Heql_sent in Heql'; compute in Heql'.
    all: remember (toValue (eval_state (sRReader IDefaultPtr_messages_right) l'))
    as msg_stack; rewrite Heql' in Heqmsg_stack; compute in Heqmsg_stack.
    all: assert (exists addr, addr = toValue (eval_state (sRReader || int_sender () ||) l))
    as [addr Heqaddr]; [eexists; reflexivity|]; rewrite <- Heqaddr;
    rewrite eql in Heqaddr; compute in Heqaddr; rewrite Heqaddr; clear Heqaddr addr.
  
    all: rewrite Heqmsg_stack, Heqmsg_state_sent;
    apply messageSentTrivial.
Admitted.

Lemma notifyLeft_noexec_proof : notifyLeft_noexec_prop vbf eb pkin nonce balance adj_balance l.
Proof.
  unfold notifyLeft_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- notifyLeft_exec_prf in Heql'.
  unfold notifyLeft_exec in Heql'.
  intros Hnoreq. remember notifyLeft_isError_proof as prf. clear Heqprf.
  unfold notifyLeft_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- notifyLeft_err_prf in Hnoreq.
  unfold notifyLeft_err in Hnoreq.
  
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

  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l'; compute; reflexivity
    ]
  end. discriminate Hnoreq.
Admitted.

(* proofs do not compute *)

End notifyLeft.

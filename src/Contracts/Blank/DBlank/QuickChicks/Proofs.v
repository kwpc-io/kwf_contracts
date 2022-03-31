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

(* Tactic Notation "destruct" "ledger" "as" ident(H) := ( 
  destruct l eqn:H; rewrite <- H in *; repeat destruct p;
  destruct c; repeat destruct p;
  destruct v; repeat destruct p;
  repeat (try destruct l0; try destruct l1; try destruct l2; try destruct l3; try destruct l4;
    try destruct l5; try destruct l6; try destruct l7);
  destruct m; repeat destruct p; destruct m0; repeat destruct p;
  destruct o; repeat destruct p; destruct o0; repeat destruct p). *)

Section constructor.
Context (mb: uint128) ( min_summa max_summa: uint128 ) (l: LedgerLRecord ).

Definition constructor_err_P :
  {t | t = isError (eval_state (UinterpreterL
  (constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l)}.
  unfold UinterpreterL, constructor_, check_owner.
  repeat auto_build_P.
Defined.

Definition constructor_err : bool.
  term_of_2 constructor_err_P constructor_err_P.
Defined.

Definition constructor_err_proof : constructor_err =
  isError (eval_state (UinterpreterL
  (constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l).
  proof_of_2 constructor_err constructor_err_P constructor_err_P.
Defined.

Lemma constructor_isError_proof :
  constructor_isError_prop mb min_summa max_summa l.
Proof.
  unfold constructor_isError_prop, constructor_requires.
  rewrite isErrorEq, <- constructor_err_proof.
  unfold constructor_err.

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

  do 7 match goal with
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
  - split; intros HH; discriminate HH.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <= 0 =>
      replace tv1 with (xIntGtb tv2 (Build_XUBInteger (n:=32) 0));
      [destruct tv2|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. reflexivity.
  - match goal with |- ?tv1 = false <-> (uint2N ?tv2 <= 0) \/ (uint2N ?tv2 > 100) =>
      replace tv1 with (andb (xIntGtb tv2 (Build_XUBInteger (n:=8) 0))
        (xIntLeb tv2 (Build_XUBInteger (n:=8) 100)));
      [destruct tv2|reflexivity]
    end.
    simpl. rewrite Bool.andb_false_iff. rewrite N.ltb_ge, N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <= 0 =>
      replace tv1 with (xIntGtb tv2 (Build_XUBInteger (n:=128) 0));
      [destruct tv2|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. reflexivity.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 > uint2N ?tv3 =>
      replace tv1 with (xIntLeb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 =>
      replace tv1 with (xIntGeb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
      replace tv1 with (Common.eqb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. reflexivity.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
      replace tv1 with (boolNegb (Common.eqb tv2 (Build_XUBInteger (n:=256) 0)));
      [destruct tv2|reflexivity]
    end.
    simpl. destruct (N.eqb_spec x 0); lia.
Defined.

Definition constructor_exec_P :
  {t | t = exec_state (UinterpreterL (
    constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l}.
  unfold UinterpreterL, constructor_, check_owner.
  repeat auto_build_P.
Defined.

Definition constructor_exec : LedgerLRecord.
  term_of_2 constructor_exec_P constructor_exec_P.
Defined.

Definition constructor_exec_prf : constructor_exec =
  exec_state (UinterpreterL (
    constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l.
  proof_of_2 constructor_exec constructor_exec_P constructor_exec_P.
Defined.

Definition constructor_unconditional_exec : LedgerLRecord.
  pose (l' := constructor_exec). unfold constructor_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma remove_conditions : (~ (constructor_requires mb min_summa max_summa l)) ->
  constructor_exec = constructor_unconditional_exec.
Proof.
  pose proof constructor_isError_proof as constructor_isError_proof'.
  pose proof constructor_err_proof as constructor_err_proof'.
  unfold constructor_err  in constructor_err_proof'.
  unfold constructor_isError_prop in  constructor_isError_proof'.
  rewrite isErrorEq in constructor_isError_proof'.

  intros Hnoreq. 
  rewrite <- constructor_isError_proof' in Hnoreq. clear constructor_isError_proof'.
  rewrite <- constructor_err_proof' in Hnoreq.

  clear constructor_err_proof'. unfold constructor_exec.

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ => 
    destruct cond;
    [ unfold xBoolIfElse at 1 , CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1 , CommonInstances.boolFunRec at 1
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end. unfold constructor_unconditional_exec.
  reflexivity.
Defined.


(* Definition constructor_exec_prop : Prop :=
let l' := exec_state (UinterpreterL (constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l in
let gs := toValue (eval_state (sRReader || givers_summa_ || ) l') in
let ids := toValue (eval_state (sRReader || investors_adj_summa_ || ) l') in
let iss := toValue (eval_state (sRReader || investors_summa_ || ) l') in
let mins := toValue (eval_state (sRReader || min_summa_ || ) l') in
let maxs := toValue (eval_state (sRReader || max_summa_ || ) l') in
let fgch := toValue (eval_state (sRReader || fromgiver_code_hash_ || ) l') in
let kch := toValue (eval_state (sRReader || kwdpool_code_hash_ || ) l') in
let fgcd := toValue (eval_state (sRReader || fromgiver_code_depth_ || ) l') in
let kcd := toValue (eval_state (sRReader || kwdpool_code_depth_ || ) l') in
let ns := toValue (eval_state (sRReader || num_investors_sent_ || ) l') in
let nr := toValue (eval_state (sRReader || num_investors_received_ || ) l') in
let cck := toValue (eval_state (sRReader || can_change_kwdpool_code_ || ) l') in
let ccf := toValue (eval_state (sRReader || can_change_fromgiver_code_ || ) l') in

(~ (constructor_requires mb min_summa max_summa l)) ->
(
  uint2N gs = 0 ). *)
   (* /\
  uint2N ids = 0 /\
  uint2N iss = 0 /\
  uint2N mins = uint2N min_summa /\
  uint2N maxs = uint2N max_summa /\
  uint2N fgch = 0 /\
  uint2N kch = 0 /\
  uint2N fgcd = 0 /\
  uint2N kcd = 0 /\
  uint2N ns = 0 /\
  uint2N nr = 0 /\
  cck = true /\
  ccf = true /\
  VMState_ι_accepted (Ledger_VMState l') = true
). *)

Definition constructor_exec_refined : LedgerLRecord := match l with 
  ((x,
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
       (x12, (x13, (x14, (x15, (x16, (x17, (x18, (x19, (x20, (x21, (x22, (x23, (x24, (x25, x26)))))))))))))))))))))))))))%core,
      (c0,
      (m,
      (m0, (x27, (x28, (x29, (a, (x30, (x31, (a0, (c, (c1, (x32, (x33, (c2, (x34, x35)))))))))))), (l0, l1))))))%xprod =>
  ((Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (min_summa,
 (max_summa,
 (x8,
 (x9,
 (x10,
 (x11,
 (x12,
 (x13,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (true,
 (true,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0,
 (Build_XUBInteger 0, (Build_XUBInteger 0, (Some false, (Build_XUBInteger 0, (Build_XUBInteger 0, x26)))))))))))))))))))))))))))%core,
  (c0,
  (m, (m0, (x27, (x28, (x29, (a, (x30, (x31, (a0, (c, (c1, (true, (x33, (c2, (x34, x35)))))))))))), (l0, l1))))))%xprod
end.

Lemma constructor_exec_refined_proof :
  constructor_unconditional_exec = constructor_exec_refined.
Proof.
  unfold constructor_unconditional_exec, constructor_exec_refined.

  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.

  compute. reflexivity.
Defined.

Lemma constructor_exec_proof : constructor_exec_prop mb min_summa max_summa l.
Proof.
  unfold constructor_exec_prop. intros Hnoreq. 

  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- constructor_exec_prf, remove_conditions,
    constructor_exec_refined_proof in Heql'; [|assumption].
  unfold constructor_exec_refined in Heql'.

  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  repeat split.

  all: rewrite Heql'; reflexivity.
Defined.

Lemma constructor_noexec_proof : constructor_noexec_prop mb min_summa max_summa l.
Proof.
  unfold constructor_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- constructor_exec_prf in Heql'.
  unfold constructor_exec in Heql'.
  intros Hnoreq. remember constructor_isError_proof as prf. clear Heqprf.
  unfold constructor_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- constructor_err_proof in Hnoreq.
  unfold constructor_err in Hnoreq.
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

End constructor.

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
  }

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



Section deployFromGiver.
Context (fgmb eb: uint128) (code : cell_)  (giver : address) (nonce : uint256) (l: LedgerLRecord).

Definition deployFromGiver_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l)}.
  unfold UinterpreterL, deployFromGiver_, check_owner.
  repeat auto_build_P.
Defined.

Definition deployFromGiver_err : bool.
  term_of_2 deployFromGiver_err_P deployFromGiver_err_P.
Defined.

Definition deployFromGiver_err_prf : deployFromGiver_err =
  isError (eval_state (UinterpreterL (
    deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l).
  proof_of_2 deployFromGiver_err deployFromGiver_err_P deployFromGiver_err_P.
Defined.

Lemma deployFromGiver_isError_proof : deployFromGiver_isError_prop fgmb eb code giver nonce l.
Proof.
  unfold deployFromGiver_isError_prop. rewrite isErrorEq.
  rewrite <- deployFromGiver_err_prf. unfold deployFromGiver_err.
  
  unfold deployFromGiver_requires.
  
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 + 2 * uint2N ?tv4 =>
      replace tv1 with (xIntGeb tv2 (xIntPlus tv3 (xIntMult (Build_XUBInteger (n:=128) 2) tv4)));
      [destruct tv2; destruct tv3; destruct tv4|reflexivity]
    end.
    simpl. rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
      replace tv1 with (Common.eqb tv2 tv3); [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. split; congruence.
  - match goal with |- ?tv1 = false <-> ?tv2 = ?tv3 =>
      replace tv1 with (negb (Common.eqb tv2 tv3)); [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. destruct x0. destruct x2. simpl. destruct (Z.eqb_spec x x1); simpl.
    + destruct (N.eqb_spec x0 x2); simpl.
      * subst x x0; intuition.
      * subst x; intuition; congruence.
    + intuition. congruence.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 >= uint2N ?tv3 =>
      replace tv1 with (Common.ltb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.ltb_ge. lia.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 <> uint2N ?tv3 =>
      replace tv1 with (Common.eqb tv2 tv3);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. reflexivity.
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 = 0 =>
      replace tv1 with (negb (Common.eqb tv2 (Build_XUBInteger 0)));
      [destruct tv2|reflexivity]
    end.
    simpl. destruct (N.eqb_spec x 0); intuition.
Defined.

Definition deployFromGiver_exec_P :
  {t | t = exec_state (UinterpreterL (
    deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l}.
  unfold UinterpreterL, deployFromGiver_, check_owner.
  do 6 auto_build_P.
  6:{ eexists; reflexivity. }
  all: repeat auto_build_P.
Defined.

Definition deployFromGiver_exec : LedgerLRecord.
  term_of_2 deployFromGiver_exec_P deployFromGiver_exec_P.
Defined.

Definition deployFromGiver_exec_prf : deployFromGiver_exec =
  exec_state (UinterpreterL (
    deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l.
  proof_of_2 deployFromGiver_exec deployFromGiver_exec_P deployFromGiver_exec_P.
Defined.


Definition deployFromGiver_unconditional_exec : LedgerLRecord.
  pose (l' := deployFromGiver_exec). unfold deployFromGiver_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma deployFromGiver_remove_conditions_helper :
  forall {A1 A2 A3 A4 A5 A6 A} (c1 c2 c3 c4 c5 c6 : bool) (v1 : A1) (v2 : A2) (v3 : A3) (v4 : A4) (v5 : A5) (v6 : A6)
  (e1 e2 e3 e4 e5 e6 : ErrorType) (a1 a2 a3 a4 a5 a6 a : A),
  match (xBoolIfElse c1 (ControlValue true v1) (ControlError e1)) with
  | ControlValue _ _ =>
    match (xBoolIfElse c2 (ControlValue true v2) (ControlError e2)) with
    | ControlValue _ _ =>
      match (xBoolIfElse c3 (ControlValue true v3) (ControlError e3)) with
      | ControlValue _ _ => 
        match (xBoolIfElse c4 (ControlValue true v4) (ControlError e4)) with
        | ControlValue _ _ => 
          match (xBoolIfElse c5 (ControlValue true v5) (ControlError e5)) with
          | ControlValue _ _ => 
            match (xBoolIfElse c6 (ControlValue true v6) (ControlError e6)) with
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
    end
  | ControlReturn _ => false
  | _ => true
  end <> true ->
  (if xBoolIfElse c1 false true then a1 else
  if xBoolIfElse c2 false true then a2 else
  if xBoolIfElse c3 false true then a3 else
  if xBoolIfElse c4 false true then a4 else
  if xBoolIfElse c5 false true then a5 else
  if xBoolIfElse c6 false true then a6 else
  a) = a.
Proof.
  intros.
  destruct c1. 2:{ exfalso. apply H. reflexivity. }
  destruct c2. 2:{ exfalso. apply H. reflexivity. }
  destruct c3. 2:{ exfalso. apply H. reflexivity. }
  destruct c4. 2:{ exfalso. apply H. reflexivity. }
  destruct c5. 2:{ exfalso. apply H. reflexivity. }
  destruct c6. 2:{ exfalso. apply H. reflexivity. }
  simpl. reflexivity.
Defined.

Lemma deployFromGiver_remove_conditions : (~ (deployFromGiver_requires fgmb eb code giver l)) ->
  deployFromGiver_exec = deployFromGiver_unconditional_exec.
Proof.
  pose proof deployFromGiver_isError_proof as deployFromGiver_isError_proof'.
  pose proof deployFromGiver_err_prf as deployFromGiver_err_proof'.
  unfold deployFromGiver_err  in deployFromGiver_err_proof'.
  unfold deployFromGiver_isError_prop in  deployFromGiver_isError_proof'.
  rewrite isErrorEq in deployFromGiver_isError_proof'.

  intros Hnoreq. 
  rewrite <- deployFromGiver_isError_proof' in Hnoreq. clear deployFromGiver_isError_proof'.
  rewrite <- deployFromGiver_err_proof' in Hnoreq.

  clear deployFromGiver_err_proof'. unfold deployFromGiver_exec, deployFromGiver_unconditional_exec.

  apply (deployFromGiver_remove_conditions_helper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnoreq).
Defined.

Lemma IDFromGiver_eqb_spec : @leibniz_eqb Interface.IDFromGiver _. Admitted.
(* Proof.
  unfold leibniz_eqb. intros a b. split.
  - intros H. destruct a, b; simpl in H; try discriminate H; try reflexivity.
    + destruct x, x0. simpl in H. destruct (N.eqb_spec x x0). subst x0. reflexivity. discriminate.
    + destruct c, c0. destruct t, t0; simpl in H; try reflexivity. discriminate H. discriminate H.
      
    +
    +
    +
  - *)

Lemma ProdStrInt_eqb_spec : @leibniz_eqb (string * nat)%type _.
Proof.
  intros [a1 a2] [b1 b2]. split.
  - intros H. simpl in H. destruct (Nat.eqb_spec a2 b2).
    2:{ destruct (CommonInstances.string_dec_bool a1 b1); discriminate H. }
    unfold CommonInstances.string_dec_bool in H. destruct (string_dec a1 b1).
    + subst a1 a2. reflexivity.
    + discriminate H.
  - intros H. injection H as H1 H2. subst b1 b2.
    simpl. rewrite Nat.eqb_refl. unfold CommonInstances.string_dec_bool.
    destruct (string_dec a1 a1). reflexivity. exfalso. apply n. reflexivity.
Defined.

Lemma deployFromGiver_exec_proof : deployFromGiver_exec_prop fgmb eb code giver nonce l.
Proof.
  unfold deployFromGiver_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) l) as l'.
  rewrite <- deployFromGiver_exec_prf, deployFromGiver_remove_conditions in Heql'.
  unfold deployFromGiver_unconditional_exec in Heql'.
  2:{ assumption. }


  repeat split.

  - destruct l. repeat destruct p.
    destruct c. repeat destruct p.
    destruct v. repeat destruct p.
    subst l'. compute. reflexivity.
  - destruct l. repeat destruct p.
    destruct c. repeat destruct p.
    destruct v. repeat destruct p.
    subst l'. compute. reflexivity.
  - 
    match goal with H : l' = exec_state _ ?l0 |- _ =>
    replace l0 with l in Heql'; [|reflexivity] end.

    match goal with H : l' = ?ex |- _ => introduce ex end.
    { do 6 auto_build_P. 6:{  auto_build_P. eexists. reflexivity.
      all: repeat auto_build_P. } all: repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq in Heql'. clear eq.

    match type of Heql' with l' = ?e => introduce e; [repeat auto_build_P|];
    extract_eq as eq; rewrite <- eq in Heql'; clear eq end.

    match type of Heql' with l' = _ _ ?e => introduce e; [repeat auto_build_P|];
    extract_eq as eq; rewrite <- eq in Heql'; clear eq end.

    remember (tvm_newContract_right _ _ _) as new_contract_r.
    remember (exec_state (rpureLWriterN _ _) _) as to_gen.

    match type of Heqto_gen with _ = ?e => introduce e;
    [repeat auto_build_P|]; extract_eq as eq; rewrite <- eq in Heqto_gen;
    clear eq end.

    remember (exec_state (sRReader
       (buildFromGiverDataInitCell_right _ _)) _) as built_cell.
    
    match type of Heql' with context [ add_new_local_index_atN "fgaddr" ?b ] =>
    remember (add_new_local_index_atN "fgaddr" b) as l'' end.

    unfold buildFromGiverDataInitCell_right, buildFromGiverDataInitCell_,
    tvm_buildDataInit_right in Heqbuilt_cell.
    Unset Printing Notations.

    match type of Heqbuilt_cell with _ = ?t => introduce t end.
    {
      unfold wrapURExpression, SML_NG32.wrapURExpression.
      auto_build_P. unfold ursus_call_with_argsL, UExpressionP_Next_LedgerableWithLArgsL,
      UExpressionP_Next_LedgerableWithRArgsL, UExpressionP0_LedgerableWithArgsL.
      C_rr_exec_P. all: repeat auto_build_P.
    }
    extract_eq as eq. rewrite <- eq in Heqbuilt_cell. clear eq.

    match type of Heqbuilt_cell with _ = exec_state _ (exec_state _ (exec_state _ ?t)) =>
    remember t as l_accepted end.

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

    rewrite eql in Heql_accepted.
    (* compute in Heql_accepted. *)
    cbv beta iota zeta delta
    -[xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush]
    in Heql_accepted.

    rewrite Heql_accepted, eql in Heqbuilt_cell.
    cbv beta iota zeta delta
    -[xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush]
    in Heqbuilt_cell.

    rewrite Heqbuilt_cell, eql in Heqto_gen.
    cbv beta iota zeta delta
    -[xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush]
    in Heqto_gen.

    rewrite Heqto_gen, eql in Heql''.
    cbv beta iota zeta delta
    -[xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush]
    in Heql''.

    pose (stck := toValue (eval_state (sRReader IDFromGiverPtr_messages_right) l')).
    assert (stck = toValue (eval_state (sRReader IDFromGiverPtr_messages_right) l')) as E.
    { reflexivity. }
    rewrite <- E.

    match goal with |- is_true (isMessageSent _ ?t _ stck) =>
    pose (addr1 := t); assert (addr1 = t) as Heqaddr1; [reflexivity|];
    rewrite <- Heqaddr1 end.

    rewrite eql in Heqaddr1.
    cbv beta iota zeta delta
    -[xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush tvmCells.hash_ addr1]
    in Heqaddr1. idtac.
    
    rewrite Heql', Heqnew_contract_r, Heql'', Heqto_gen, eql in E.
    cbv beta iota zeta delta
    -[xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush tvmCells.hash_ stck]
    in E. idtac.

    match type of E with _ = ?mp [?ind] ← ?stk => 
    remember ind as addr2
    end.

    replace addr1 with addr2. rewrite E.
    replace (toValue (eval_state (sRReader || lock_time_ ||) l)) with x8.
    replace (toValue (eval_state (sRReader || unlock_time_ ||) l)) with x9.
    apply messageSentTrivial.

    + apply IDFromGiver_eqb_spec.
    + rewrite eql. reflexivity.
    + rewrite eql. reflexivity.
    + rewrite Heqaddr1. rewrite Heqaddr2.
      repeat rewrite insert_find. reflexivity.
      all: apply ProdStrInt_eqb_spec.
Abort.

Lemma deployFromGiver_noexec_proof : deployFromGiver_noexec_prop fgmb eb code giver nonce l.
Proof.
  unfold deployFromGiver_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- deployFromGiver_exec_prf in Heql'.
  unfold deployFromGiver_exec in Heql'.
  intros Hnoreq. remember deployFromGiver_isError_proof as prf. clear Heqprf.
  unfold deployFromGiver_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- deployFromGiver_err_prf in Hnoreq.
  unfold deployFromGiver_err in Hnoreq.

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
Defined.

End deployFromGiver.



Section acknowledgeDeploy.
Context (giver : address) (nonce : uint256) (l : LedgerLRecord).

Definition acknowledgeDeploy_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l)}.
  unfold UinterpreterL, acknowledgeDeploy_, check_giver.
  repeat auto_build_P.
Defined.

Definition acknowledgeDeploy_err : bool.
  term_of_2 acknowledgeDeploy_err_P acknowledgeDeploy_err_P.
Defined.

Definition acknowledgeDeploy_err_prf : acknowledgeDeploy_err =
  isError (eval_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l).
  proof_of_2 acknowledgeDeploy_err acknowledgeDeploy_err_P acknowledgeDeploy_err_P.
Defined.

Lemma acknowledgeDeploy_isError_proof : acknowledgeDeploy_isError_prop giver nonce l.
Proof.
  unfold acknowledgeDeploy_isError_prop. rewrite isErrorEq.
  rewrite <- acknowledgeDeploy_err_prf. unfold acknowledgeDeploy_err.
  
  unfold acknowledgeDeploy_requires.
  
  repeat (replace (exec_state _ _) with l; [|reflexivity]).

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
  - rewrite isErrorEq. match goal with |- _ <-> ?er = true => introduce er end.
    { unfold UinterpreterL, check_giver, new_lvalueL. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end; simpl; intuition.
Defined.

Definition acknowledgeDeploy_exec_P :
  {t | t = exec_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l}.
  unfold UinterpreterL, acknowledgeDeploy_, check_giver.
  do 3 auto_build_P. 5:{ eexists; reflexivity. }
  all: repeat auto_build_P.
Defined.

Definition acknowledgeDeploy_exec : LedgerLRecord.
  term_of_2 acknowledgeDeploy_exec_P acknowledgeDeploy_exec_P.
Defined.

Definition acknowledgeDeploy_exec_prf : acknowledgeDeploy_exec =
  exec_state (UinterpreterL (
    acknowledgeDeploy_ giver nonce)) l.
  proof_of_2 acknowledgeDeploy_exec acknowledgeDeploy_exec_P acknowledgeDeploy_exec_P.
Defined.

(* TODO : long check *)

(* Lemma acknowledgeDeploy_exec_proof : acknowledgeDeploy_exec_prop giver nonce l.
Proof.
  destruct l eqn:E. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.

  unfold acknowledgeDeploy_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- E, <- acknowledgeDeploy_exec_prf in Heql'.
  unfold acknowledgeDeploy_exec in Heql'.

  remember acknowledgeDeploy_isError_proof as prf. clear Heqprf.
  unfold acknowledgeDeploy_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- E, <- prf, <- acknowledgeDeploy_err_prf in Hnoreq. clear prf.
  unfold acknowledgeDeploy_err in Hnoreq. subst l.

  (* destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  match goal with |- context [ (?a, ?b)%xprod ] =>
  pose (l_orig := (a, b)%xprod) end. *)

  repeat match goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end <> true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity
    ]
  end.

  clear Hnoreq.
  subst l'. destruct x14. intuition.
Defined. *)

(* TODO : long check *)

(* Lemma acknowledgeDeploy_noexec_proof : acknowledgeDeploy_noexec_prop giver nonce l.
Proof.

  unfold acknowledgeDeploy_noexec_prop. remember (exec_state _ _) as l'.
  rewrite <- acknowledgeDeploy_exec_prf in Heql'.
  unfold acknowledgeDeploy_exec in Heql'.
  intros Hnoreq. remember acknowledgeDeploy_isError_proof as prf. clear Heqprf.
  unfold acknowledgeDeploy_isError_prop in prf. rewrite isErrorEq in prf.
  rewrite <- prf in Hnoreq. clear prf.
  rewrite <- acknowledgeDeploy_err_prf in Hnoreq.
  unfold acknowledgeDeploy_err in Hnoreq.

  generalize Heql' Hnoreq. clear Heql' Hnoreq.

  refine (match l with ((x, (x0, (x1, (x2, (x3, (x4, (x5, (x6,
  (x7, (x8, (x9, (x10, (x11, (x12, (x13, (x14, (x15, (x16, x17))))))))))))))))))%core,
  (c0, (m, (m0, (x18, (x19,
  (x20, (a, (x21, (x22, (a0, (c, (c1, (x23, (x24, (c2, (x25, x26)))))))))))),
  (l0, l1))))))%xprod => _ end).

  intros.

  (* assert (l = ((x, (x0, (x1, (x2, (x3, (x4, (x5, (x6,
  (x7, (x8, (x9, (x10, (x11, (x12, (x13, (x14, (x15, (x16, x17))))))))))))))))))%core,
  (c0, (m, (m0, (x18, (x19,
  (x20, (a, (x21, (x22, (a0, (c, (c1, (x23, (x24, (c2, (x25, x26)))))))))))),
  (l0, l1))))))%xprod). 
  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  Show Proof. *)
  
  repeat lazymatch goal with
  Hnoreq : match xBoolIfElse ?cond _ _ with _ => _ end = true |- _ =>
    destruct cond;
    [ unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Hnoreq;
      unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql'
    | unfold xBoolIfElse at 1, CommonInstances.boolFunRec at 1 in Heql';
      subst l'; compute; reflexivity
    ]
  end. discriminate Hnoreq.
Defined. *)

End acknowledgeDeploy.



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
Admitted.

(* TODO : long compute *)

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
Abort.

  
End notifyRight.



Section acknowledgeFinalizeRight.
Context (giver : address) (nonce : uint256) (dead_giver : XBool) (l: LedgerLRecord).

Definition acknowledgeFinalizeRight_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    acknowledgeFinalizeRight_ giver nonce dead_giver)) l)}.
  unfold UinterpreterL, acknowledgeFinalizeRight_, check_giver.
  repeat auto_build_P.
Defined.

Definition acknowledgeFinalizeRight_err : bool.
  term_of_2 acknowledgeFinalizeRight_err_P acknowledgeFinalizeRight_err_P.
Defined.

Definition acknowledgeFinalizeRight_err_prf : acknowledgeFinalizeRight_err =
  isError (eval_state (UinterpreterL (
    acknowledgeFinalizeRight_ giver nonce dead_giver)) l).
  proof_of_2 acknowledgeFinalizeRight_err acknowledgeFinalizeRight_err_P acknowledgeFinalizeRight_err_P.
Defined.

Lemma acknowledgeFinalizeRight_isError_proof : acknowledgeFinalizeRight_isError_prop giver nonce dead_giver l.
Proof.
  unfold acknowledgeFinalizeRight_isError_prop. rewrite isErrorEq.
  rewrite <- acknowledgeFinalizeRight_err_prf. unfold acknowledgeFinalizeRight_err.
  
  unfold acknowledgeFinalizeRight_requires.

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
  - rewrite isErrorEq. match goal with |- _ <-> ?er = true => introduce er end.
    { unfold UinterpreterL, check_giver, new_lvalueL. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end; simpl; intuition.
Defined.

Definition acknowledgeFinalizeRight_exec_P :
  {t | t = exec_state (UinterpreterL (acknowledgeFinalizeRight_ giver nonce dead_giver)) l}.
  unfold UinterpreterL, acknowledgeFinalizeRight_, check_giver.
  do 3 auto_build_P. 5:{ eexists; reflexivity. }
  all: repeat auto_build_P.
Defined.

Definition acknowledgeFinalizeRight_exec : LedgerLRecord.
  term_of_2 acknowledgeFinalizeRight_exec_P acknowledgeFinalizeRight_exec_P.
Defined.

Definition acknowledgeFinalizeRight_exec_prf : acknowledgeFinalizeRight_exec =
  exec_state (UinterpreterL (acknowledgeFinalizeRight_ giver nonce dead_giver)) l.
  proof_of_2 acknowledgeFinalizeRight_exec acknowledgeFinalizeRight_exec_P acknowledgeFinalizeRight_exec_P.
Defined.

Definition acknowledgeFinalizeRight_unconditional_exec : LedgerLRecord.
  pose (l' := acknowledgeFinalizeRight_exec). unfold acknowledgeFinalizeRight_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma notifyRight_remove_conditions_helper :
  forall {A1 A} (c1 : bool) (v1 : A1)
  (e1 : ErrorType) (a1 a : A),
  match (xBoolIfElse c1 (ControlValue true v1) (ControlError e1)) with
  | ControlValue _ _ => false
  | ControlReturn _ => false
  | _ => true
  end <> true ->
  (if xBoolIfElse c1 false true then a1 else a) = a.
Proof.
  intros.
  destruct c1. 2:{ exfalso. apply H. reflexivity. }
  simpl. reflexivity.
Defined.

Lemma acknowledgeFinalizeRight_remove_conditions : (~ (acknowledgeFinalizeRight_requires giver nonce dead_giver l)) ->
  acknowledgeFinalizeRight_exec = acknowledgeFinalizeRight_unconditional_exec.
Proof.
  pose proof acknowledgeFinalizeRight_isError_proof as acknowledgeFinalizeRight_isError_proof'.
  pose proof acknowledgeFinalizeRight_err_prf as acknowledgeFinalizeRight_err_proof'.
  unfold acknowledgeFinalizeRight_err  in acknowledgeFinalizeRight_err_proof'.
  unfold acknowledgeFinalizeRight_isError_prop in  acknowledgeFinalizeRight_isError_proof'.
  rewrite isErrorEq in acknowledgeFinalizeRight_isError_proof'.

  intros Hnoreq. 
  rewrite <- acknowledgeFinalizeRight_isError_proof' in Hnoreq. clear acknowledgeFinalizeRight_isError_proof'.
  rewrite <- acknowledgeFinalizeRight_err_proof' in Hnoreq.

  clear acknowledgeFinalizeRight_err_proof'. unfold acknowledgeFinalizeRight_exec, acknowledgeFinalizeRight_unconditional_exec.

  apply (notifyRight_remove_conditions_helper _ _ _ _ _ Hnoreq).
Admitted.

Lemma acknowledgeFinalizeRight_exec_proof : acknowledgeFinalizeRight_exec_prop giver nonce dead_giver l.
Proof.

  unfold acknowledgeFinalizeRight_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- acknowledgeFinalizeRight_exec_prf,
  acknowledgeFinalizeRight_remove_conditions in Heql'.
  unfold acknowledgeFinalizeRight_unconditional_exec in Heql'.
  2:{ assumption. }

  match type of Heql' with _ = exec_state _ ?t =>
  remember t as l'' end.
  replace (uint2N (toValue (eval_state (sRReader || num_investors_received_ ||) l)))
  with (uint2N (toValue (eval_state (sRReader || num_investors_received_ ||) l''))).
  2:{ rewrite Heql''. destruct l. repeat destruct p. reflexivity. }
  clear Heql'' Hnoreq l. rename l'' into l.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  
  destruct dead_giver.
  {
    rewrite eql in Heql'. compute in Heql'. rewrite Heql', eql. compute.
    split. reflexivity. destruct x15. reflexivity.
  }
  {
    rewrite eql in Heql'. compute in Heql'. rewrite Heql', eql. compute.
    split. reflexivity. destruct x15. reflexivity.
  }
Defined.

End acknowledgeFinalizeRight.



Section acknowledgeFinalizeLeft.
Context (pkin : uint256 ) (nonce : uint256) (l: LedgerLRecord).

Definition acknowledgeFinalizeLeft_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    acknowledgeFinalizeLeft_ pkin nonce)) l)}.
  unfold UinterpreterL, acknowledgeFinalizeLeft_, check_investor.
  repeat auto_build_P.
Defined.

Definition acknowledgeFinalizeLeft_err : bool.
  term_of_2 acknowledgeFinalizeLeft_err_P acknowledgeFinalizeLeft_err_P.
Defined.

Definition acknowledgeFinalizeLeft_err_prf : acknowledgeFinalizeLeft_err =
  isError (eval_state (UinterpreterL (
    acknowledgeFinalizeLeft_ pkin nonce)) l).
  proof_of_2 acknowledgeFinalizeLeft_err acknowledgeFinalizeLeft_err_P acknowledgeFinalizeLeft_err_P.
Defined.

Lemma acknowledgeFinalizeLeft_isError_proof : acknowledgeFinalizeLeft_isError_prop pkin nonce l.
Proof.
  unfold acknowledgeFinalizeLeft_isError_prop. rewrite isErrorEq.
  rewrite <- acknowledgeFinalizeLeft_err_prf. unfold acknowledgeFinalizeLeft_err.
  
  unfold acknowledgeFinalizeLeft_requires.

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
  - rewrite isErrorEq. match goal with |- _ <-> ?er = true => introduce er end.
    { unfold UinterpreterL, check_investor. repeat auto_build_P. }
    extract_eq as eq. rewrite <- eq. clear eq.
    match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end; simpl; intuition.
Defined.

Definition acknowledgeFinalizeLeft_exec_P :
  {t | t = exec_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l}.
  unfold UinterpreterL, acknowledgeFinalizeLeft_, check_investor.
  repeat auto_build_P.
Defined.

Definition acknowledgeFinalizeLeft_exec : LedgerLRecord.
  term_of_2 acknowledgeFinalizeLeft_exec_P acknowledgeFinalizeLeft_exec_P.
Defined.

Definition acknowledgeFinalizeLeft_exec_prf : acknowledgeFinalizeLeft_exec =
  exec_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l.
  proof_of_2 acknowledgeFinalizeLeft_exec acknowledgeFinalizeLeft_exec_P acknowledgeFinalizeLeft_exec_P.
Defined.

Definition acknowledgeFinalizeLeft_unconditional_exec : LedgerLRecord.
  pose (l' := acknowledgeFinalizeLeft_exec). unfold acknowledgeFinalizeLeft_exec in l'.
  match goal with l' := context [ if _ then _ else exec_state ?a ?b ] |- _ =>
  clear l'; exact (exec_state a b) end.
Defined.

Lemma notifyRight_remove_conditions_helper :
  forall {A1 A} (c1 : bool) (v1 : A1)
  (e1 : ErrorType) (a1 a : A),
  match (xBoolIfElse c1 (ControlValue true v1) (ControlError e1)) with
  | ControlValue _ _ => false
  | ControlReturn _ => false
  | _ => true
  end <> true ->
  (if xBoolIfElse c1 false true then a1 else a) = a.
Proof.
  intros.
  destruct c1. 2:{ exfalso. apply H. reflexivity. }
  simpl. reflexivity.
Defined.

Lemma acknowledgeFinalizeLeft_remove_conditions : (~ (acknowledgeFinalizeLeft_requires pkin nonce l)) ->
  acknowledgeFinalizeLeft_exec = acknowledgeFinalizeLeft_unconditional_exec.
Proof.
  pose proof acknowledgeFinalizeLeft_isError_proof as acknowledgeFinalizeLeft_isError_proof'.
  pose proof acknowledgeFinalizeLeft_err_prf as acknowledgeFinalizeLeft_err_proof'.
  unfold acknowledgeFinalizeLeft_err  in acknowledgeFinalizeLeft_err_proof'.
  unfold acknowledgeFinalizeLeft_isError_prop in  acknowledgeFinalizeLeft_isError_proof'.
  rewrite isErrorEq in acknowledgeFinalizeLeft_isError_proof'.

  intros Hnoreq. 
  rewrite <- acknowledgeFinalizeLeft_isError_proof' in Hnoreq. clear acknowledgeFinalizeLeft_isError_proof'.
  rewrite <- acknowledgeFinalizeLeft_err_proof' in Hnoreq.

  clear acknowledgeFinalizeLeft_err_proof'. unfold acknowledgeFinalizeLeft_exec, acknowledgeFinalizeLeft_unconditional_exec.

  apply (notifyRight_remove_conditions_helper _ _ _ _ _ Hnoreq).
Admitted.

Lemma acknowledgeFinalizeLeft_exec_proof : acknowledgeFinalizeLeft_exec_prop pkin nonce l.
Proof.

  unfold acknowledgeFinalizeLeft_exec_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  rewrite <- acknowledgeFinalizeLeft_exec_prf,
  acknowledgeFinalizeLeft_remove_conditions in Heql'.
  unfold acknowledgeFinalizeLeft_unconditional_exec in Heql'.
  2:{ assumption. }

  match type of Heql' with _ = exec_state _ (exec_state _ (exec_state _ ?t)) =>
  remember t as l'' end.
  replace (uint2N (toValue (eval_state (sRReader || num_investors_received_ ||) l)))
  with (uint2N (toValue (eval_state (sRReader || num_investors_received_ ||) l''))).
  2:{ rewrite Heql''. destruct l. repeat destruct p. reflexivity. }
  clear Heql'' Hnoreq l. rename l'' into l.

  destruct l eqn:eql. rewrite <- eql in *. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.
  
  rewrite eql in Heql'. compute in Heql'. rewrite Heql', eql. compute.
  split. reflexivity. destruct x15. reflexivity.
Abort.

End acknowledgeFinalizeLeft.



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


(* 
Section setFundCode.
Context ( rb: uint128 ) (tffc : uint32) (code : cell_ ) ( l: LedgerLRecord ).

Definition setFundCode_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    setFundCode_ (RESPAWN_BALANCE_:=rb) (KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_:=tffc) code)) l)}.
  unfold UinterpreterL, setFundCode_, check_owner.
  repeat auto_build_P.
Defined.

Definition setFundCode_err : bool.
  term_of_2 setFundCode_err_P setFundCode_err_P.
Defined.

Definition setFundCode_err_prf : setFundCode_err =
  isError (eval_state (UinterpreterL (
    setFundCode_ (RESPAWN_BALANCE_:=rb) (KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_:=tffc) code)) l).
  proof_of_2 setFundCode_err setFundCode_err_P setFundCode_err_P.
Defined.

Lemma setFundCode_isError_proof : setFundCode_isError_prop rb code l.
Proof.
  unfold setFundCode_isError_prop. rewrite isErrorEq.
  rewrite <- setFundCode_err_prf. unfold setFundCode_err.
  
  unfold setFundCode_requires.
  
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N rb =>
      replace tv1 with (xIntGeb tv2 rb);
      [destruct tv2; destruct rb|reflexivity]
    end.
    simpl. rewrite N.leb_gt. lia.
  - lazymatch goal with |- ?tv1 = false <->
    uint2N ?tv2 < uint2N ?tv3 \/ uint2N ?tv4 > uint2N ?tv5 =>
    replace tv1 with (andb (xIntGeb tv2 tv3) (xIntLeb tv2 tv5));
    [destruct tv2; destruct tv3; destruct tv5|reflexivity]
    end.
    simpl. rewrite Bool.andb_false_iff. do 2 rewrite N.leb_gt. lia.
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
      replace tv1 with (Common.eqb tv3 tv2);
      [destruct tv2; destruct tv3|reflexivity]
    end.
    simpl. rewrite N.eqb_neq. split; intros n H; congruence.
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
  
End setFundCode. *)



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

  Opaque xIntPlus xIntMinus Common.hmapFindWithDefault xHMapInsert hmapPush.
  rewrite eql in Heql'. compute in Heql'.
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
  compute in y.

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



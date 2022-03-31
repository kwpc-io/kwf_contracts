Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

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

Lemma R_uneq_exec_P_helper : forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false)
  (l l0 l1 : LedgerLRecord),
  l0 = exec_state (sRReader r1) l ->
  l1 = exec_state (sRReader r2) l0 ->
  l1 = exec_state (sRReader (uneqb r1 r2)) l.
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H0. subst l2. simpl. destruct (simple_state_run (sRReader r2) l0) eqn:Er2.
  simpl in H1. subst l2. dependent destruction c. simpl. reflexivity.
Defined.

Ltac R_uneq_exec_P :=
  lazymatch goal with
  | |- {t | t = exec_state (sRReader (@uneqb _ _ _ _ _ _ _ _ _ _ ?X ?Hbeq ?r1 ?r2)) ?l} =>
    let l0 := fresh "l" in
    let l1 := fresh "l" in
    assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
    [|assert {t | t = exec_state (sRReader r2) l0} as [l1 ?];
      [|exists l1; apply (@R_uneq_exec_P_helper X Hbeq r1 r2 l l0 l1);
        assumption
      ]
    ]
  end.

Goal forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false) (l : LedgerLRecord),
  {t | t = exec_state (sRReader || {r1} != {r2} ||) l}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_uneq_exec_P.
Abort.

Lemma R_uneq_eval_false_P_helper : forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false)
  (l l0 : LedgerLRecord) (v1 v2 : X),
  v1 = toValue (eval_state (sRReader r1) l) ->
  l0 = exec_state (sRReader r1) l ->
  v2 = toValue (eval_state (sRReader r2) l0) ->
  boolNegb (eqb v1 v2) = toValue (eval_state (sRReader (uneqb r1 r2)) l).
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H0. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H0. subst x.
  simpl in H1. subst l1. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H2. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H2. subst x.
  simpl. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym. reflexivity.
Defined.

Ltac R_uneq_eval_false_P :=
  lazymatch goal with
  | |- {t | t = toValue (eval_state (sRReader (@uneqb _ _ _ _ _ _ _ _ _ _ ?X ?Hbeq ?r1 ?r2)) ?l)} =>
    let l0 := fresh "l" in
    let v1 := fresh "v" in
    let v2 := fresh "v" in
    assert {t | t = toValue (eval_state (sRReader r1) l)} as [v1 ?];
    [|assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
      [|assert {t | t = toValue (eval_state (sRReader r2) l0)} as [v2 ?];
        [|exists (boolNegb (eqb v1 v2)); apply (@R_uneq_eval_false_P_helper X Hbeq r1 r2 l l0 v1 v2);
          assumption
        ]
      ]
    ]
  end.

Goal forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false) (l : LedgerLRecord),
  {t | t = toValue (eval_state (sRReader || {r1} != {r2} ||) l)}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_uneq_eval_false_P.
Abort.

Lemma R_ueq_exec_P_helper : forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false)
  (l l0 l1 : LedgerLRecord),
  l0 = exec_state (sRReader r1) l ->
  l1 = exec_state (sRReader r2) l0 ->
  l1 = exec_state (sRReader (ueqb r1 r2)) l.
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H0. subst l2. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H1. subst l2. simpl. reflexivity.
Defined.

Ltac R_ueq_exec_P :=
  lazymatch goal with
  | |- {t | t = exec_state (sRReader (@ueqb _ _ _ _ _ _ _ _ _ _ ?X ?Hbeq ?r1 ?r2)) ?l} =>
    let l0 := fresh "l" in
    let l1 := fresh "l" in
    assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
    [|assert {t | t = exec_state (sRReader r2) l0} as [l1 ?];
      [|exists l1; apply (@R_ueq_exec_P_helper X Hbeq r1 r2 l l0 l1);
        assumption
      ]
    ]
  end.

Goal forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false) (l : LedgerLRecord),
  {t | t = exec_state (sRReader || {r1} == {r2} ||) l}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_ueq_exec_P.
Abort.

Lemma R_ueq_eval_false_P_helper : forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false)
  (l l0 : LedgerLRecord) (v1 v2 : X),
  v1 = toValue (eval_state (sRReader r1) l) ->
  l0 = exec_state (sRReader r1) l ->
  v2 = toValue (eval_state (sRReader r2) l0) ->
  eqb v1 v2 = toValue (eval_state (sRReader (ueqb r1 r2)) l).
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H0. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H0. subst x.
  simpl in H1. subst l1. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H2. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H2. subst x.
  simpl. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym. reflexivity.
Defined.

Ltac R_ueq_eval_false_P :=
  lazymatch goal with
  | |- {t | t = toValue (eval_state (sRReader (@ueqb _ _ _ _ _ _ _ _ _ _ ?X ?Hbeq ?r1 ?r2)) ?l)} =>
    let l0 := fresh "l" in
    let v1 := fresh "v" in
    let v2 := fresh "v" in
    assert {t | t = toValue (eval_state (sRReader r1) l)} as [v1 ?];
    [|assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
      [|assert {t | t = toValue (eval_state (sRReader r2) l0)} as [v2 ?];
        [|exists (eqb v1 v2); apply (@R_ueq_eval_false_P_helper X Hbeq r1 r2 l l0 v1 v2);
          assumption
        ]
      ]
    ]
  end.

Goal forall {X} `{XBoolEquable boolean X} (r1 r2 : URValue X false) (l : LedgerLRecord),
  {t | t = toValue (eval_state (sRReader || {r1} == {r2} ||) l)}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_ueq_eval_false_P.
Abort.

Lemma R_uge_exec_P_helper : forall {n} (r1 r2 : URValue (XUBInteger n) false)
  (l l0 l1 : LedgerLRecord),
  l0 = exec_state (sRReader r1) l ->
  l1 = exec_state (sRReader r2) l0 ->
  l1 = exec_state (sRReader (ugeb r1 r2)) l.
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H. subst l2. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H0. subst l2. simpl. reflexivity.
Defined.

Ltac R_uge_exec_P :=
  lazymatch goal with
  | |- {t | t = exec_state (sRReader (@ugeb _ _ _ _ _ _ _ _ ?X ?Hifr _ _ ?r1 ?r2)) ?l} =>
    let l0 := fresh "l" in
    let l1 := fresh "l" in
    assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
    [|assert {t | t = exec_state (sRReader r2) l0} as [l1 ?];
      [|exists l1; apply (@R_uge_exec_P_helper _ r1 r2 l l0 l1);
        assumption
      ]
    ]
  end.

Goal forall {n} (r1 r2 : URValue (XUBInteger n) false) (l : LedgerLRecord),
  {t | t = exec_state (sRReader || {r1} >= {r2} ||) l}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_uge_exec_P.
Abort.

Lemma R_uge_eval_false_P_helper : forall {n} (r1 r2 : URValue (XUBInteger n) false)
  (l l0 : LedgerLRecord) (v1 v2 : XUBInteger n),
  v1 = toValue (eval_state (sRReader r1) l) ->
  l0 = exec_state (sRReader r1) l ->
  v2 = toValue (eval_state (sRReader r2) l0) ->
  xIntGeb v1 v2 = toValue (eval_state (sRReader (ugeb r1 r2)) l).
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H0. subst l1. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H1. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H1. subst x0.
  simpl. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym.
  simpl in H. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H. subst x.
  reflexivity.
Defined.

Ltac R_uge_eval_false_P :=
  lazymatch goal with
  | |- {t | t = toValue (eval_state (sRReader (@ugeb _ _ _ _ _ _ _ _ ?X ?Hifr _ _ ?r1 ?r2)) ?l)} =>
    let l0 := fresh "l" in
    let v1 := fresh "v" in
    let v2 := fresh "v" in
    assert {t | t = toValue (eval_state (sRReader r1) l)} as [v1 ?];
    [|assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
      [|assert {t | t = toValue (eval_state (sRReader r2) l0)} as [v2 ?];
        [|exists (xIntGeb v1 v2); apply (@R_uge_eval_false_P_helper _ r1 r2 l l0 v1 v2);
          assumption
        ]
      ]
    ]
  end.

Goal forall {n} (r1 r2 : URValue (XUBInteger n) false) (l : LedgerLRecord),
  {t | t = toValue (eval_state (sRReader || {r1} >= {r2} ||) l)}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_uge_eval_false_P.
Abort.

Lemma R_uplus_exec_P_helper : forall {I} `{intFunRec_gen boolean I}
  (r1 r2 : URValue I false)
  (l l0 l1 : LedgerLRecord),
  l0 = exec_state (sRReader r1) l ->
  l1 = exec_state (sRReader r2) l0 ->
  l1 = exec_state (sRReader (uplus r1 r2)) l.
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H0. subst l2. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H1. subst l2. simpl. reflexivity.
Defined.

Ltac R_uplus_exec_P :=
  lazymatch goal with
  | |- {t | t = exec_state (sRReader (@uplus _ _ _ _ _ _ _ _ ?X ?Hifr _ _ ?r1 ?r2)) ?l} =>
    let l0 := fresh "l" in
    let l1 := fresh "l" in
    assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
    [|assert {t | t = exec_state (sRReader r2) l0} as [l1 ?];
      [|exists l1; apply (@R_uplus_exec_P_helper X Hifr r1 r2 l l0 l1);
        assumption
      ]
    ]
  end.

Goal forall {I} `{intFunRec_gen boolean I} (r1 r2 : URValue I false) (l : LedgerLRecord),
  {t | t = exec_state (sRReader || {r1} + {r2} ||) l}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_uplus_exec_P.
Abort.

Lemma R_uplus_eval_false_P_helper : forall {I} `{intFunRec_gen boolean I}
  (r1 r2 : URValue I false)
  (l l0 : LedgerLRecord) (v1 v2 : I),
  v1 = toValue (eval_state (sRReader r1) l) ->
  l0 = exec_state (sRReader r1) l ->
  v2 = toValue (eval_state (sRReader r2) l0) ->
  xIntPlus v1 v2 = toValue (eval_state (sRReader (uplus r1 r2)) l).
Proof.
  helper_start. destruct (simple_state_run _ _) eqn:Er1. dependent destruction c.
  simpl in H1. subst l1. simpl.
  destruct (simple_state_run (sRReader r2) l0) eqn:Er2. dependent destruction c.
  simpl in H2. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H2. subst i0.
  simpl. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym.
  simpl in H0. unfold solution_left, eq_rect_r, eq_rect, Logic.eq_sym in H0. subst i.
  reflexivity.
Defined.

Ltac R_uplus_eval_false_P :=
  lazymatch goal with
  | |- {t | t = toValue (eval_state (sRReader (@uplus _ _ _ _ _ _ _ _ ?X ?Hifr _ _ ?r1 ?r2)) ?l)} =>
    let l0 := fresh "l" in
    let v1 := fresh "v" in
    let v2 := fresh "v" in
    assert {t | t = toValue (eval_state (sRReader r1) l)} as [v1 ?];
    [|assert {t | t = exec_state (sRReader r1) l} as [l0 ?];
      [|assert {t | t = toValue (eval_state (sRReader r2) l0)} as [v2 ?];
        [|exists (xIntPlus v1 v2); apply (@R_uplus_eval_false_P_helper X Hifr r1 r2 l l0 v1 v2);
          assumption
        ]
      ]
    ]
  end.

Goal forall {I} `{intFunRec_gen boolean I} (r1 r2 : URValue I false) (l : LedgerLRecord),
  {t | t = toValue (eval_state (sRReader || {r1} + {r2} ||) l)}.
  intros. unfold wrapURValueL, SML_NG32.wrapURValue. R_uplus_eval_false_P.
Abort.

Ltac auto_build := first [R_uneq_eval_false_P | R_ueq_eval_false_P
  | R_uge_eval_false_P | R_uplus_eval_false_P
  | R_uneq_exec_P | R_ueq_exec_P
  | R_uge_exec_P | R_uplus_exec_P] + auto_build_P.

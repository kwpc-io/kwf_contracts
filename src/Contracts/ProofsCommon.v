Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Bool.

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

Class eqb_spec A `{inst : XBoolEquable bool A} := {
  eqb_spec_intro : forall (a b : A), Common.eqb a b = true <-> a = b
}.

Lemma eqb_spec_reflect {A} `{eqb_spec A} :
  forall a b : A, reflect (a = b) (Common.eqb a b).
Proof.
  intros a b. destruct (Common.eqb a b) eqn:E; constructor.
  - destruct H. rewrite eqb_spec_intro0 in E. assumption.
  - intros eq. destruct H. rewrite <- eqb_spec_intro0, E in eq.
    discriminate eq.
Defined.

Lemma messageSentTrivial : forall {A} `{eqb_spec A}
  (msg : OutgoingMessage A)
  (msgMap : queue (OutgoingMessage A))
  (stateMap : mapping address (queue (OutgoingMessage A)))
  (ind : address),
  is_true (isMessageSent msg ind 0 (stateMap [ind] ← (hmapPush msg msgMap))).
Admitted.

Lemma insert_find : forall {K V} `{eqb_spec K}
  (vd v : V) (k : K) (li : CommonInstances.listPair K V),
  Common.hmapFindWithDefault vd k (xHMapInsert k v li) = v.
Admitted.

#[export]
Instance boolean_eqb_spec : eqb_spec boolean.
Proof.
  constructor. intros [] []; intuition.
Defined.

#[export]
Instance uint8_eqb_spec : forall n, eqb_spec (XUBInteger n).
Proof.
  constructor. intros a b. destruct a, b. simpl.
  destruct (N.eqb_spec x x0).
  - split. subst x0. reflexivity. reflexivity.
  - split. intros. discriminate. intros. injection H. intros.
    exfalso. congruence.
Defined.

#[export]
Instance cell_eqb_spec : eqb_spec cell_.
Proof.
  constructor. intros a b. unfold Common.eqb, cellBoolEq.
  destruct (cellEq_Dec _ _). destruct dec.
  - subst b. split; reflexivity.
  - split. intros H; discriminate H. intros eq. exfalso. congruence.
Defined.

#[export]
Instance IDFromGiver_eqb_spec : eqb_spec Interface.IDFromGiver.
Proof.
  constructor. intros a b. destruct a; (destruct b;
  try (split; [intros H; simpl in H; discriminate H
  |intros H; discriminate H])).
  all: unfold Common.eqb, IDFromGiver_booleq; (
    repeat match goal with |- context [Common.eqb ?x1 ?x2] =>
    destruct (eqb_spec_reflect x1 x2); [subst x2|
    simpl; split;
    [ intros; discriminate
    | let H := fresh "H" in intros H; injection H; intros; exfalso; congruence ] ] end
  );
  split; reflexivity.
Defined.

#[export]
Instance ProdStrInt_eqb_spec : eqb_spec (string * nat)%type.
Proof.
  constructor. intros [a1 a2] [b1 b2]. split.
  - intros H. simpl in H. destruct (Nat.eqb_spec a2 b2).
    2:{ destruct (CommonInstances.string_dec_bool a1 b1); discriminate H. }
    unfold CommonInstances.string_dec_bool in H. destruct (string_dec a1 b1).
    + subst a1 a2. reflexivity.
    + discriminate H.
  - intros H. injection H as H1 H2. subst b1 b2.
    simpl. rewrite Nat.eqb_refl. unfold CommonInstances.string_dec_bool.
    destruct (string_dec a1 a1). reflexivity. exfalso. apply n. reflexivity.
Defined.

#[export]
Instance PhantomType_eqb_spec : eqb_spec PhantomType.
Proof.
  constructor. intros [] []. split; reflexivity.
Defined.

#[export]
Instance IKWFundParticipant_eqb_spec : eqb_spec Interface.IKWFundParticipant.
Proof.
  constructor. intros a b. destruct a; (destruct b;
  try (split; [intros H; simpl in H; discriminate H
  |intros H; discriminate H])).
  all: unfold Common.eqb, IKWFundParticipant_booleq; (
    repeat match goal with |- context [Common.eqb ?x1 ?x2] =>
    destruct (eqb_spec_reflect x1 x2); [subst x2|
    simpl; split;
    [ intros; discriminate
    | let H := fresh "H" in intros H; injection H; intros; exfalso; congruence ] ] end
  );
  split; reflexivity.
Defined.

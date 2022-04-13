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

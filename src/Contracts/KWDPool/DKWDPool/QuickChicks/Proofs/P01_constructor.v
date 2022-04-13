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
(* Local Open Scope string_scope. *)
Local Open Scope xlist_scope.

Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DKWDPool.QuickChicks.QCEnvironment.
Require Import DKWDPool.QuickChicks.Props.
Require Import UMLang.ExecGenerator.

Require Import Contracts.ProofsCommon.

Section constructor.
Context ( MB: uint128 ) ( GFM: uint128 )
( final_address: optional address ) ( l: LedgerLRecord ) .

Definition constructor_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    constructor_ (KWMessages_ι_KWD_MIN_BALANCE_:= MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l)}.
  unfold UinterpreterL, constructor_, check_owner.
  repeat auto_build_P.
Defined.

Definition constructor_err : bool.
  term_of_2 constructor_err_P constructor_err_P.
Defined.

Definition constructor_err_prf : constructor_err =
  isError (eval_state (UinterpreterL (
    constructor_ (KWMessages_ι_KWD_MIN_BALANCE_:= MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l).
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
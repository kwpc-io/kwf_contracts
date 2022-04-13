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

Section sendFunds.
Context (EB: uint128) (code :  cell_  ) ( l: LedgerLRecord ).

Definition sendFunds_err_P :
  {t | t = isError (eval_state (UinterpreterL (
    sendFunds_ (KWMessages_ι_EPSILON_BALANCE_ := EB) code)) l)}.
  unfold UinterpreterL, sendFunds_, check_owner, check_init, check_fund.
  repeat auto_build_P.
Defined.

Definition sendFunds_err : bool.
  term_of_2 sendFunds_err_P sendFunds_err_P.
Defined.

Definition sendFunds_err_prf : sendFunds_err =
  isError (eval_state (UinterpreterL (
    sendFunds_ (KWMessages_ι_EPSILON_BALANCE_ := EB) code)) l).
  proof_of_2 sendFunds_err sendFunds_err_P sendFunds_err_P.
Defined.

Lemma sendFunds_isError_proof : sendFunds_isError_prop EB code l.
Proof.
  unfold sendFunds_isError_prop. rewrite isErrorEq.
  rewrite <- sendFunds_err_prf. unfold sendFunds_err.
  
  unfold sendFunds_requires.
  
  repeat (replace (exec_state _ _) with l; [|reflexivity]).

  repeat match goal with
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
  - match goal with |- ?tv1 = false <-> uint2N ?tv2 < uint2N ?tv3 + uint2N ?tv4 + uint2N EB =>
    replace tv1 with (xIntGeb tv2 (xIntPlus (xIntPlus tv3 tv4) EB));
    [destruct tv2; destruct tv3; destruct tv4; destruct EB|reflexivity] end.
    simpl. apply N.leb_gt.
  - match goal with |- ?tv1 = false <-> ?tv2 = None =>
    replace tv1 with (negb (Common.eqb tv2 default));
    [destruct tv2|reflexivity] end.
    + split; intros; discriminate.
    + simpl. split; reflexivity.
  - reflexivity.
  - match goal with |- ?tv1 = false <-> ?tv2 <> ?tv3 =>
    replace tv1 with (Common.eqb tv2 tv3);
    [destruct tv2; destruct tv3|reflexivity] end.
    simpl. destruct x2. destruct x0. simpl.
    destruct (Z.eqb_spec x x1). 2:{ simpl. split; intros; congruence. }
    destruct (N.eqb_spec x0 x2); simpl; split; intros; congruence.
  - reflexivity.
Defined.

End sendFunds.
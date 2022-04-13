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

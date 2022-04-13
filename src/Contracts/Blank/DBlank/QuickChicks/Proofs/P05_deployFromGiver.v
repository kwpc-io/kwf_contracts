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

    + rewrite eql. reflexivity.
    + rewrite eql. reflexivity.
    + rewrite Heqaddr1. rewrite Heqaddr2.
      destruct a0.
      repeat unshelve erewrite insert_find.
      all: try apply ProdStrInt_eqb_spec. reflexivity.
Unshelve. all: let n := numgoals in guard n=0. Admitted.

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

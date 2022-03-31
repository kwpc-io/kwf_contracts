(* Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Bool. 
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

Require Import Project.CommonQCEnvironment.
Require Import DKWDPool.QuickChicks.QCEnvironment.
Require Import DKWDPool.QuickChicks.Props.
Require Import DKWDPool.QuickChicks.Generators.

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

Lemma eqb_uint_spec : forall a b : uint, reflect (a = b) (eqb a b).
Proof.
  intros. unfold eqb, xIntBoolEquable, uintFunRec.
  apply N.eqb_spec.
Defined.

Lemma eqb_uint_iff : forall a b : uint, a = b <-> eqb a b = true.
Proof.
  intros. destruct (eqb_uint_spec a b).
  - split. reflexivity. intros _. assumption.
  - split. intros. exfalso. apply n. assumption.
    intros. discriminate.
Defined.

Lemma neqb_uint_iff : forall a b : uint, a <> b <-> eqb a b = false.
Proof.
  intros. destruct (eqb_uint_spec a b).
  - split. intros n. exfalso. apply n. assumption.
    intros. discriminate.
  - split. reflexivity. intros _. assumption.
Defined.

Lemma eqb_field_type_spec : forall a b : (Z * XUBInteger 256)%type,
  reflect (a = b) (eqb a b).
Proof.
  intros. unfold eqb, pair_xbool_equable, eqb, xIntBoolEquable, intFunRec,
    xubint_booleq, tvmTypes.xubint_booleq_obligation_1.
    destruct a as [al ar]. destruct b as [bl br]. simpl.
  destruct (Z.eqb_spec al bl); simpl.
  destruct ar. destruct br.
  destruct (N.eqb_spec x x0).
  - constructor. subst bl x0. reflexivity.
  - constructor. intros H. injection H as H1 H2. apply n. assumption.
  - constructor. intros H. injection H as H1 H2. apply n. assumption.
Defined.

Lemma eqb_field_type_iff : forall a b : (Z * XUBInteger 256)%type,
  a = b <-> eqb a b = true.
Proof.
  intros. destruct (eqb_field_type_spec a b).
  - split. reflexivity. intros _. assumption.
  - split. intros. exfalso. apply n. assumption.
    intros. discriminate.
Defined.

Lemma neqb_field_type_iff : forall a b : (Z * XUBInteger 256)%type,
  a <> b <-> eqb a b = false.
Proof.
  intros. destruct (eqb_field_type_spec a b).
  - split. intros n. exfalso. apply n. assumption.
    intros. discriminate.
  - split. reflexivity. intros _. assumption.
Defined.

Lemma geb_uint_spec : forall a b : uint, reflect (b <= a) (xIntGeb a b).
Proof.
  intros. unfold xIntGeb, xIntBoolEquable, uintFunRec, N.le, N.leb.
  destruct (b ?= a); constructor.
  - intros n. discriminate.
  - intros n. discriminate.
  - intros n. apply n. reflexivity.
Defined.

Lemma geb_uint_iff : forall a b : uint, b <= a <-> xIntGeb a b = true.
Proof.
  intros a b. destruct (geb_uint_spec a b).
  - split. reflexivity. intros _. assumption.
  - split. intros. exfalso. apply n. assumption.
    intros. discriminate.
Defined.

Lemma isErrorEq : forall {R b} (cr : ControlResult R b),
  CommonQCEnvironment.isError cr <-> isError cr = true.
Proof. unfold isError, CommonQCEnvironment.isError. destruct cr; intuition. Defined.

Lemma constructor_isError_proof (MB :  uint128) (GFM :  uint128)
  ( final_address: optional address ) 
  ( l: LedgerLRecord ) : constructor_isError_prop MB GFM final_address l.
Proof.
  unfold constructor_isError_prop.

  (* rewrite constructor isError *)
  rewrite isErrorEq.
  introduce (isError (eval_state (UinterpreterL (constructor_
    (KWD_MIN_BALANCE_:= MB) (GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l)).
  { unfold constructor_, check_owner, UinterpreterL.
    unfold wrapURValueL, tvm_msg_pubkey, tvmFunc.tvm_pubkey, tvmFunc.tvm_balance,
    fund_address__right. repeat auto_build. }
  extract_eq as eq. rewrite <- eq. clear eq.

  unfold constructor_requires.
  introduce (toValue (eval_state (sRReader || msg_pubkey () ||) l)).
  { unfold wrapURValueL, tvm_msg_pubkey. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq. clear eq.

  introduce (toValue (eval_state (sRReader || tvm_pubkey () ||) l)).
  { unfold wrapURValueL, tvmFunc.tvm_pubkey. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq. clear eq.

  introduce (toValue (eval_state (sRReader || tvm_balance () ||) l)).
  { unfold wrapURValueL, tvmFunc.tvm_balance. repeat auto_build_P. }
  extract_eq as eq. rewrite <- eq. clear eq.

  rewrite eqb_uint_iff. rewrite neqb_uint_iff.
  rewrite N.lt_nge. rewrite geb_uint_iff.

  do 3 destruct (projTransEmbed _).
  destruct MB. destruct GFM. unfold uint2N.
  
  unfold eqb at 1, xubint_booleq, tvmTypes.xubint_booleq_obligation_1,
    xInt0, uintFunRec.
  destruct (eqb x 0). { simpl. split; auto. }
  unfold boolNegb at 1, xBoolIfElse at 1 2, boolFunRec, xBoolTrue.

  unfold eqb at 1. destruct (eqb x0 x). 2:{ simpl. split; auto. }
  unfold xBoolIfElse at 1 2, boolFunRec, xBoolTrue.

  unfold xIntPlus at 1, xubint_intFunRec.
  unfold xIntPlus, uintFunRec, xIntGeb. destruct (x2 + x3 <=? x1).
  2:{ split; auto. }

  match goal with |- match _ ?v _ _ with _ => _ end = _ <-> _ =>
    replace v
    with (negb (eqb (DKWDPool_ι_fund_address__ (Ledger_MainState l)) default))
  end; [|reflexivity]. rewrite eqb_field_type_iff. destruct (eqb _ _); simpl; split; auto.
  intuition.
Defined.


Lemma constructor_setFinal_address_proof
                           ( MB: uint128 )
                           ( GFM: uint128 )
                           ( final_address: optional address )
                           ( final_address': address ) 
                           ( l: LedgerLRecord ) : 
                           constructor_setFinal_address_prop MB GFM final_address final_address' l.
Proof.
  unfold constructor_setFinal_address_prop.
  intros [Hnoreq Hfin].

  introduce (exec_state (UinterpreterL (constructor
    (KWD_MIN_BALANCE_:= MB) (GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l).
  { unfold constructor, check_owner, UinterpreterL. 
    unfold wrapURValueL, tvm_msg_pubkey, tvmFunc.tvm_pubkey, tvmFunc.tvm_balance,
      fund_address__right.
    repeat auto_build.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  remember (constructor_isError_proof MB GFM final_address l) as iserror_prop.
  clear Heqiserror_prop. unfold constructor_isError_prop in iserror_prop.
  rewrite <- iserror_prop in Hnoreq. clear iserror_prop.
  rewrite isErrorEq in Hnoreq.

  introduce (isError (eval_state (UinterpreterL (constructor
    (KWD_MIN_BALANCE_:= MB) (GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l)).
  { unfold constructor, check_owner, UinterpreterL. 
    unfold wrapURValueL, tvm_msg_pubkey, tvmFunc.tvm_pubkey, tvmFunc.tvm_balance,
      fund_address__right.
      repeat auto_build.
  }
  extract_eq as eq. rewrite <- eq in Hnoreq. clear eq.

  do 3 (match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end;
  [ unfold xBoolIfElse at 1, boolFunRec
  | simpl in Hnoreq; exfalso; apply Hnoreq; reflexivity]).
  destruct (boolNegb (eqb (projTransEmbed l) default)).
  2:{ simpl in Hnoreq. exfalso. apply Hnoreq. reflexivity. }
  unfold xBoolIfElse at 1, boolFunRec. clear Hnoreq. subst final_address.

  remember (exec_state (Uinterpreter _) _) as l'. clear Heql'.
  destruct l'. repeat destruct p. simpl.
  destruct c. repeat destruct p. simpl.
  compute. reflexivity.
Defined.

Section initialize.
Context 
(lock_time : ( XUInteger32 )) 
(unlock_time : ( XUInteger32 ))
(quant : ( XUInteger128 ))
(rate : ( XUInteger8 ))
(kwf_lock_time : ( XUInteger32 )) 
( l: LedgerLRecord ).

Lemma initialize_isError_proof :
  initialize_isError_prop lock_time unlock_time quant rate kwf_lock_time l.
Proof.
  unfold initialize_isError_prop.

  rewrite isErrorEq. 
  
  introduce (isError (eval_state (UinterpreterL (initialize_
  lock_time unlock_time quant rate kwf_lock_time)) l)).
  { unfold UinterpreterL, initialize_, check_fund, wrapURValueL,
    fund_address__right, tvm_msg_sender.
    repeat auto_build.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  unfold initialize_requires.

  introduce (toValue (eval_state (sRReader || int_sender () ||) l)).
  { Unset Printing Notations. unfold wrapURValueL, tvm_msg_sender.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  introduce (toValue (eval_state (sRReader || fund_address_ ||) l)).
  { Unset Printing Notations. unfold fund_address__right.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  replace (toValue (eval_state (sRReader (uneg || initialized_ ||)) l))
  with (negb (toValue (eval_state (sRReader || initialized_ ||) l))).
  2:{ reflexivity. }

  introduce (toValue (eval_state (sRReader || initialized_ ||) l)).
  { Unset Printing Notations. unfold initialized__right.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  replace (exec_state (sRReader (uneg || initialized_ ||)) l)
  with (exec_state (sRReader || initialized_ ||) l). 2:{ reflexivity. }

  introduce (exec_state (sRReader || initialized_ ||) l).
  { Unset Printing Notations. unfold initialized__right.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  replace (toValue (eval_state (sRReader (ultb tvmFunc.tvm_now (URScalar lock_time))) l))
  with (ltb (toValue (eval_state (sRReader || tvm_now () ||) l)) lock_time).
  2:{ reflexivity. }

  introduce (toValue (eval_state (sRReader || tvm_now () ||) l)).
  { Unset Printing Notations. unfold wrapURValueL, tvmFunc.tvm_now.
    repeat auto_build_P.
  }
  extract_eq as eq. rewrite <- eq. clear eq.

  rewrite neqb_field_type_iff. destruct (eqb _ _). 2:{ split; auto. }
  unfold xBoolIfElse, boolFunRec.
  
  destruct (projTransEmbed _). 1:{ split; auto. }
  unfold negb. unfold ltb, xubint_ordered, tvmTypes.xubint_ordered_obligation_1.
  destruct (projTransEmbed _). destruct lock_time. unfold ltb, xIntOrdered, uintFunRec.
  match goal with |- ?a = _ <-> _ => replace a with (negb (x <? x0)) end.
  2:{ destruct (x <? x0); reflexivity. } simpl.
  rewrite <- N.leb_antisym. rewrite N.leb_le.
  split; intros. lia. decompose sum H. discriminate. discriminate. lia.
Defined.

Definition initialize_err_P :
  {t | t = isError (eval_state (UinterpreterL (initialize_
  lock_time unlock_time quant rate kwf_lock_time)) l)}.
  unfold UinterpreterL, initialize_, check_fund.
  repeat auto_build_P.
Defined.

Definition initialize_err : bool.
  term_of_2 initialize_err_P initialize_err_P.
Defined.

Definition initialize_err_proof : initialize_err =
  isError (eval_state (UinterpreterL (initialize_
  lock_time unlock_time quant rate kwf_lock_time)) l).
  proof_of_2 initialize_err initialize_err_P initialize_err_P.
Defined.

Definition initialize_exec_P :
  {t | t = exec_state (UinterpreterL (initialize_
  lock_time unlock_time quant rate kwf_lock_time)) l}.
  unfold UinterpreterL, initialize_, check_fund. repeat auto_build_P.
Defined.

Definition initialize_exec : LedgerLRecord.
  term_of_2 initialize_exec_P initialize_exec_P.
Defined.

Definition initialize_exec_proof : initialize_exec =
exec_state (UinterpreterL (initialize_
lock_time unlock_time quant rate kwf_lock_time)) l.
  proof_of_2 initialize_exec initialize_exec_P initialize_exec_P.
Defined.

Lemma initialize_setInitialize_proof :
  initialize_setInitialize_prop lock_time unlock_time quant rate kwf_lock_time l.
Proof.
  unfold initialize_setInitialize_prop. intros Hnoreq.
  remember initialize_isError_proof as eq.
  clear Heqeq. unfold initialize_isError_prop in eq. rewrite isErrorEq in eq.
  rewrite <- eq in Hnoreq. clear eq.
  rewrite <- initialize_err_proof in Hnoreq. unfold initialize_err in Hnoreq.

  rewrite <- initialize_exec_proof. unfold initialize_exec.

  do 3 (match goal with |- context [ xBoolIfElse ?c _ _ ] => destruct c end;
  try (exfalso; apply Hnoreq; reflexivity); unfold xBoolIfElse at 1, boolFunRec;
  unfold xBoolIfElse at 1, boolFunRec in Hnoreq).
  
  destruct l. repeat destruct p. destruct c. repeat destruct p. compute. reflexivity.
Defined.

Lemma initialize_setBlankParams_proof :
  initialize_setBlankParams_prop lock_time unlock_time quant rate kwf_lock_time l.
Proof.
  unfold initialize_setBlankParams_prop. intros Hnoreq.
  remember (exec_state (UinterpreterL _) _) as l'.
  remember initialize_isError_proof as eq.
  clear Heqeq. unfold initialize_isError_prop in eq. rewrite isErrorEq in eq.
  rewrite <- eq in Hnoreq. clear eq.

  rewrite <- initialize_err_proof in Hnoreq. unfold initialize_err in Hnoreq.
  rewrite <- initialize_exec_proof in Heql'. unfold initialize_exec in Heql'.

  do 3 (match type of Hnoreq with context [ xBoolIfElse ?c _ _ ] => destruct c end;
  try (exfalso; apply Hnoreq; reflexivity); unfold xBoolIfElse at 1, boolFunRec in Heql';
  unfold xBoolIfElse at 1, boolFunRec in Hnoreq).

  destruct l. repeat destruct p. destruct c. repeat destruct p.

  repeat try split; subst l'; compute; reflexivity.

Defined.

End initialize.

Section receive.
Context (DMF : uint16) ( GFM  : uint128) (  EB : uint128 ) ( l: LedgerLRecord ).

(* Check maybeFunBool .
Instance option_bool_spec : forall {I}, IfElseSpec (option (OutgoingMessage I)) maybeFunBool.
intros. split. intros. unfold xBoolIfElse, maybeFunBool, Common.maybeFunBool_obligation_3.
destruct c; simpl; reflexivity.
Defined. *)

Instance XMaybeAddress : IfElseSpec (XMaybe address) _. (* for generator to work *)
split. destruct c; reflexivity.
Defined.

Definition receive_err_P :
  {t | t = isError (eval_state (UinterpreterL (receive
  ( DEFAULT_MSG_FLAGS_ := DMF) (GAS_FOR_FUND_MESSAGE_ := GFM) (EPSILON_BALANCE_ := EB) )) l)}.
  unfold UinterpreterL, receive, check_init.

  match goal with |- context [ {{ require_ ((tvm_now () < lock_time_), { _ } ); { ?e } }} ] =>
  remember e end.

  repeat auto_build_P.
Defined.

Definition receive_err : bool.
  term_of_2 receive_err_P receive_err_P.
Defined.

Definition receive_err_proof : receive_err =
  isError (eval_state (UinterpreterL (receive
  ( DEFAULT_MSG_FLAGS_ := DMF) (GAS_FOR_FUND_MESSAGE_ := GFM) (EPSILON_BALANCE_ := EB) )) l).
  proof_of_2 receive_err receive_err_P receive_err_P.
Defined.

Lemma receive_isError_proof : receive_isError_prop DMF GFM EB l.
Proof.
  unfold receive_isError_prop, receive_requires. rewrite isErrorEq.
  rewrite <- receive_err_proof. unfold receive_err.
  unfold receive_requires.

  case_eq (toValue (eval_state (sRReader || initialized_ ||) l)); intros eq.
  2:{ rewrite eq at 1 2. simpl. intuition. }
  rewrite eq at 1 2. clear eq.
  unfold xBoolIfElse at 1, boolFunRec.

  replace (exec_state (sRReader || initialized_ ||) l) with l.
  2:{ reflexivity. }
  replace (toValue
  (eval_state
     (sRReader
        || balance_ ==
           {SML_NG32.apply_pure
              (SML_NG32.sInject uint optional tuple mapping xInt0)
              Build_XUBInteger} ||) l))
  with (eqb (toValue
  (eval_state
     (sRReader
        || balance_ ||) l))
    xInt0); [|reflexivity].
  
  case_eq (toValue (eval_state (sRReader || balance_ ||) l)). intros x eq.
  rewrite eq at 1 2. clear eq. unfold eqb at 1, xubint_booleq, tvmTypes.xubint_booleq_obligation_1,
    xInt0 at 1, xubint_intFunRec at 1.
  assert (@uint2N 256 (@Build_XUBInteger 256 x) = 0 <-> eqb x xInt0 = true) as eq.
  { simpl. rewrite N.eqb_eq. reflexivity. } rewrite eq at 1. clear eq.
  destruct (eqb x xInt0). 2:{ simpl. intuition. }
  unfold xBoolIfElse at 1, boolFunRec.

  replace (exec_state _ _) with l; [|reflexivity].
  replace (toValue (eval_state (sRReader || int_value () >= quant_ ||) l))
  with (xIntGeb (toValue (eval_state (sRReader || int_value () ||) l))
            (toValue (eval_state (sRReader || quant_ ||) l))); [|reflexivity].
  destruct (toValue (eval_state (sRReader || int_value () ||) l)) eqn:Eintv.
  case_eq (toValue (eval_state (sRReader || quant_ ||) l)). intros x' eq.
  rewrite eq at 1 2. clear eq.
  unfold xIntGeb at 1, xubint_intFunRec at 1, xIntGeb at 1, xubint_intFunRec at 1, uintFunRec at 1.
  assert (uint2N (n := 256) (Build_XUBInteger (n := 256) x0) < uint2N (Build_XUBInteger (n := 256) x')
  <-> x' <=? x0 = false) as eq. { simpl. rewrite N.leb_gt. reflexivity. }
  rewrite eq at 1. destruct (x' <=? x0) eqn:E.
  2:{ simpl. rewrite E. simpl. intuition. }
  unfold xBoolIfElse at 1, boolFunRec.

  replace (exec_state _ _) with l; [|reflexivity]. Check @xIntGeb.
  replace (toValue
  (eval_state
     (sRReader
        || tvm_balance () >=
           (int_value () +
            {SML_NG32.sInject uint optional tuple mapping GFM}) +
           {SML_NG32.sInject uint optional tuple mapping EB}
        ||) l))
  with (xIntGeb (toValue (eval_state (sRReader || tvm_balance () ||) l))
    (xIntPlus (xIntPlus (toValue (eval_state (sRReader || int_value () ||) l)) GFM) EB)).
  2:{ reflexivity. }
  replace (toValue
  (eval_state
     (sRReader
        || tvm_balance () >=
           (int_value () +
            {SML_NG32.sInject uint optional tuple mapping GFM}) +
           {SML_NG32.sInject uint optional tuple mapping EB}
        ||) l))
  with (xIntGeb (toValue (eval_state (sRReader || tvm_balance () ||) l))
    (xIntPlus (xIntPlus (toValue (eval_state (sRReader || int_value () ||) l)) GFM) EB)).
  2:{ reflexivity. }
  destruct (toValue (eval_state (sRReader || tvm_balance () ||) l)).
  clear eq.
  replace (toValue (eval_state (sRReader || int_value () ||) l)) with (Build_XUBInteger (n:=128) x0).
  assert ((uint2N (n:=128) (Build_XUBInteger (n:=128) x1) <
    uint2N (n:=128) (Build_XUBInteger (n:=128) x0) + (uint2N (n:=128) GFM + uint2N (n:=128) EB)) <->
  (xIntGeb (Build_XUBInteger (n:=128) x1)
    (xIntPlus (xIntPlus (Build_XUBInteger (n:=128) x0) GFM) EB) = false)) as eq.
  { destruct GFM. destruct EB. unfold xIntPlus, xubint_intFunRec, xIntPlus, uintFunRec,
    xIntGeb. rewrite N.leb_gt. simpl. lia.
  } rewrite eq. clear eq. destruct (xIntGeb (Build_XUBInteger x1)
  (xIntPlus (xIntPlus (Build_XUBInteger x0) GFM) EB)).
  2:{ unfold xBoolIfElse at 1, boolFunRec. simpl. intuition. }
  unfold xBoolIfElse at 1, boolFunRec.

  replace (exec_state _ _) with l; [|reflexivity].
  replace (toValue
  (eval_state (sRReader || tvm_now () < lock_time_ ||) l))
  with (ltb (toValue (eval_state (sRReader || tvm_now () ||) l))
    (toValue (eval_state (sRReader || lock_time_ ||) l))); [|reflexivity].
  destruct (toValue (eval_state (sRReader || tvm_now () ||) l)).
  destruct (toValue (eval_state (sRReader || lock_time_ ||) l)).
  assert ((uint2N (n:=128) (Build_XUBInteger (n:=128) x2) >=
    uint2N (n:=128) (Build_XUBInteger (n:=128) x3)) <->
  (ltb (Build_XUBInteger (n:=256) x2) (Build_XUBInteger (n:=256) x3) = false)) as eq.
  { simpl. rewrite N.ltb_ge. lia. }
  rewrite eq. clear eq.
  Set Printing All.
  destruct (ltb (Build_XUBInteger (n:=256) x2) (Build_XUBInteger (n:=256) x3)).
  2:{ simpl. intuition. } clear Eintv. remember (eval_state _ _). simpl in y.
  dependent destruction y. simpl. intuition.
Defined.

End receive.
   *)
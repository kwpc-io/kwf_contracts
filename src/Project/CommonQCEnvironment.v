Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmCells.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

(*string*)

Derive Show for ascii.
Derive Shrink for ascii.
Derive GenSized for ascii.

Derive Show for string.
Derive Shrink for string.
Derive GenSized for string.

Derive Show for unit.
Derive Shrink for unit.
Derive GenSized for unit.

Local Open  Scope N_scope.

Notation " x 'deciever' " := ( N.mul x 1 ) (at level 100).

(*move these two instances to another file*)
#[global, program]  
Instance commonConsts: KWMessagesCommonConsts.
Next Obligation.
refine (Build_XUBInteger 180). (* MIN_VOTING_TIME *)
Defined.
Next Obligation.
refine (Build_XUBInteger 345600). (* TIME_FOR_SETCODE_PREPARE *)
Defined.
Next Obligation.
refine (Build_XUBInteger 259200). (* TIME_FOR_FUNDS_COLLECTING *)
Defined.
Next Obligation.
refine (Build_XUBInteger (5 deciever)). (* VOTING_FEE *)
Defined.
Next Obligation.
refine (Build_XUBInteger 64). (* MSG_VALUE_BUT_FEE_FLAGS *)
Defined.
Next Obligation.
refine (Build_XUBInteger 0). (* DEFAULT_MSG_FLAGS *)
Defined.
Next Obligation.
refine (Build_XUBInteger 128). (* ALL_BALANCE_MSG_FLAG *)
Defined.
Next Obligation.
refine (Build_XUBInteger (50 deciever) ). (* FG_MIN_BALANCE *)
Defined.
Next Obligation.
refine (Build_XUBInteger (5 deciever) ). (* GAS_FOR_FUND_MESSAGE *)
Defined.
Next Obligation.
refine (Build_XUBInteger (50 deciever) ).  (* KWD_MIN_BALANCE *)
Defined.
Next Obligation.
refine (Build_XUBInteger (5 deciever) ). (* GAS_FOR_PARTICIPANT_MESSAGE *)
Defined.
Next Obligation.
refine (Build_XUBInteger (5 deciever) ). (* EPSILON_BALANCE *)
Defined.
Next Obligation.
refine (Build_XUBInteger (500 deciever) ). (* RESPAWN_BALANCE *)
Defined.
Next Obligation.
refine (Build_XUBInteger (200 deciever) ). (* BLANK_MIN_BALANCE *)
Defined.
(*Next Obligation.
refine (Build_XUBInteger 1). (* FEE_SEPARATE_MSG_FLAGS *)
Defined. *)
Fail Next Obligation.

#[global, program] 
Instance commonErrors: KWErrorsCommonErrors.
Next Obligation.
refine  101.
Defined.
Next Obligation.
refine  102.
Defined.
Next Obligation.
refine  103.
Defined.
Next Obligation.
refine  104.
Defined.
Next Obligation.
refine  105.
Defined.
Next Obligation.
refine  106.
Defined.
Next Obligation.
refine  107.
Defined.
Next Obligation.
refine  108.
Defined.
Next Obligation.
refine  109.
Defined.
Next Obligation.
refine  110.
Defined.
Next Obligation.
refine  111.
Defined.
Next Obligation.
refine  112.
Defined.
Next Obligation.
refine  113.
Defined.
Next Obligation.
refine  114.
Defined.
Next Obligation.
refine  115.
Defined.
Next Obligation.
refine  116.
Defined.
Next Obligation.
refine  117.
Defined.
Next Obligation.
refine  118.
Defined.
Next Obligation.
refine  119.
Defined.
Next Obligation.
refine  120.
Defined.
Next Obligation.
refine  121.
Defined.
Next Obligation.
refine  122.
Defined.
Next Obligation.
refine  123.
Defined.
Next Obligation.
refine  124.
Defined.
Next Obligation.
refine  125.
Defined.
Next Obligation.
refine  126.
Defined.
Next Obligation.
refine  127.
Defined.
Next Obligation.
refine  128.
Defined.
Next Obligation.
refine  129.
Defined.
Next Obligation.
refine  130.
Defined.
Next Obligation.
refine  131.
Defined.
Next Obligation.
refine  132.
Defined.
Next Obligation.
refine  133.
Defined.
Next Obligation.
refine  134.
Defined.
Fail Next Obligation.

Derive Show for xprod.
Derive Shrink for xprod.
Derive GenSized for xprod.

Derive Show for prod.
Derive Shrink for prod.
Derive GenSized for prod.

(* Derive Show for option.
Derive Shrink for option.
Derive GenSized for option. *)

(*isotypes*)

#[local]
Instance iso_show : forall X Y`{IsoTypes X Y}`{Show Y},  Show X.
intros.
split.
intros.
refine (show (x2y X0)).
Defined.

#[local]
Instance iso_shrink : forall X Y`{IsoTypes X Y}`{Shrink Y}, Shrink X.
intros.
split.
intros.
pose proof (shrink (x2y X0)).
refine (List.map y2x X1).
Defined.

#[local]
Instance iso_genSized : forall X Y`{IsoTypes X Y}`{GenSized Y}, GenSized X.
intros.
split.
intros.
pose proof (arbitrarySized H1 : G Y).
refine (fmap y2x X0).
Defined.

#[local]
Remove Hints iso_show : typeclass_instances.
#[local]
Remove Hints iso_shrink : typeclass_instances.
#[local]
Remove Hints iso_genSized : typeclass_instances.

(* sum *)

#[global]
Instance sum_show : forall X Y`{Show X }`{Show Y}, Show (X + Y).
intros.
split.
intros.
destruct X0.
refine ( "left: " ++ (show x))%string.
refine ( "right: " ++ (show y))%string.
Defined.

#[global]
Instance sum_shrink : forall X Y`{Shrink X}`{Shrink Y}, Shrink (X+Y).
intros.
split.
intros.
destruct X0.
pose proof (shrink x).
refine (List.map inl X0).
pose proof (shrink y).
refine (List.map inr X0).
Defined.

#[global]
Instance sum_genSized : forall X Y`{GenSized X}`{GenSized Y}, GenSized (X+Y).
intros.
split.
intros.
pose proof (arbitrarySized H1: G bool).
Search (forall X Y, G X -> (X -> G Y) -> G Y).
eapply bindGen. { exact X0. }
intros b. destruct b. 
-
pose proof (arbitrarySized H1: G X).
refine (fmap inl X1).
-
pose proof (arbitrarySized H1: G Y).
refine (fmap inr X1).
Defined.

(*uint*)

Definition uint_n_to_uint {n} (x: XUBInteger n) : XUInteger.
dependent destruction x.
exact x.
Defined.

#[global]
Instance iso_uint: forall n, IsoTypes (XUBInteger n) (XUInteger).
intros.
esplit with (x2y := fun x => uint_n_to_uint x ) (y2x := Build_XUBInteger); try reflexivity.
extensionality x.
unfold compose.
dependent destruction x.
reflexivity.
Defined.

#[global]
Instance iso_option: forall X, IsoTypes (option X) (unit + X).
intros.
esplit with (x2y := fun x => match x with
                             | Some x => inr x
                             | None => inl tt end  ) (y2x := fun y =>  match y with
                                                             | inr x => Some x
                                                             | inl tt => None end); try reflexivity.
extensionality x. unfold compose.
destruct x; try destruct u; reflexivity.
extensionality y. unfold compose.
destruct y; reflexivity.
Defined.

#[global]
Instance option_gensized: forall X`{GenSized X}, GenSized (option X).
intros.
eapply iso_genSized.
eapply iso_option.
eapply sum_genSized.
apply GenSizedunit.
apply H.
Defined.


#[global]
Instance uint_n_show: forall n, Show (XUBInteger n) .
intros.
eapply iso_show.
eapply iso_uint.
apply showN.
Defined.

#[global]
Instance uint_n_shrink: forall n, Shrink (XUBInteger n) .
intros.
eapply iso_shrink.
eapply iso_uint.
apply shrinkN.
Defined.

#[global]
Instance uint_n_genSized: forall n, GenSized (XUBInteger n) .
intros.
eapply iso_genSized.
eapply iso_uint.
apply genNSized.
Defined.

(*messages*)

Definition fromMessage {I} (m: OutgoingMessage I): (unit*InternalMessageParamsLRecord)+(I*InternalMessageParamsLRecord).
destruct m.
refine (inl (tt,i)).
refine (inr (i0,i)).
Defined.

Definition toMessage {I} (m: (unit*InternalMessageParamsLRecord)+(I*InternalMessageParamsLRecord)) : OutgoingMessage I.
destruct m. destruct p.
refine (EmptyMessage _ i).
destruct p.
refine (OutgoingInternalMessage i0 i).
Defined.

#[global]
Instance iso_OutgoingMessage: forall I , IsoTypes (OutgoingMessage I) ((unit*InternalMessageParamsLRecord)+I*InternalMessageParamsLRecord).
intros.
esplit with (x2y := fromMessage )
            (y2x := toMessage); try reflexivity.
all: unfold compose.            
extensionality m.
destruct m.
simpl. destruct p. simpl. destruct u. reflexivity.
simpl. destruct p. reflexivity.
extensionality m.
destruct m.
simpl. reflexivity.
simpl. reflexivity.
Defined.

(*cells*)

#[global]
Instance iso_cell: forall n , IsoTypes (CellSliceBuilder n) TvmCell_.
intros.
esplit with (x2y := undressBuilder )
            (y2x := Build_CellSliceBuilder _); try reflexivity.
extensionality x.             
destruct x; reflexivity.
Defined.

Derive Show for TvmCell_.
Derive Shrink for TvmCell_.
Derive GenSized for TvmCell_.

(*cell_*)

#[global]
Instance cell_show: Show cell_.
eapply iso_show.
eapply iso_cell.
apply ShowTvmCell_.
Defined.

#[global]
Instance cell_shrink: Shrink cell_.
eapply iso_shrink.
eapply iso_cell.
apply ShrinkTvmCell_.
Defined.

#[global]
Instance cell_genSized: GenSized cell_.
eapply iso_genSized.
eapply iso_cell.
apply GenSizedTvmCell_.
Defined.

(*builder_*)

#[global]
Instance builder_show: Show builder_.
eapply iso_show.
eapply iso_cell.
apply ShowTvmCell_.
Defined.

#[global]
Instance builder_shrink: Shrink builder_.
eapply iso_shrink.
eapply iso_cell.
apply ShrinkTvmCell_.
Defined.

#[global]
Instance builder_genSized: GenSized builder_.
eapply iso_genSized.
eapply iso_cell.
apply GenSizedTvmCell_.
Defined.

(*outgoing message*)

#[global]
Instance OutgoingMessage_show: forall I`{Show I}, Show (OutgoingMessage I).
intros.
eapply iso_show.
eapply iso_OutgoingMessage.
eapply sum_show.
eapply Showprod.
eapply Showprod.
Defined.

#[global]
Instance OutgoingMessage_shrink: forall I`{Shrink I}, Shrink (OutgoingMessage I).
intros.
eapply iso_shrink.
eapply iso_OutgoingMessage.
eapply sum_shrink.
eapply Shrinkprod.
eapply Shrinkprod.
Defined.

#[global]
Instance OutgoingMessage_genSized: forall I`{GenSized I}, GenSized (OutgoingMessage I).
intros.
eapply iso_genSized.
eapply iso_OutgoingMessage.
eapply sum_genSized.
eapply GenSizedprod.
eapply GenSizedprod.
Defined.

(* Print Instances GenSized. *)


(*interfaces*)

Require Import Interfaces.IBlank.IBlank.Interface.
Derive Show for IBlank.
Derive Shrink for IBlank.
Derive GenSized for IBlank.

Require Import Interfaces.IKWFund.IKWFund.Interface.
Derive Show for IKWFund.
Derive Shrink for IKWFund.
Derive GenSized for IKWFund.

Require Import Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Derive Show for IKWFundParticipant.
Derive Shrink for IKWFundParticipant.
Derive GenSized for IKWFundParticipant.

Require Import Contracts.KWDPool.DKWDPool.Interface.
Derive Show for IDKWDPool.
Derive Shrink for IDKWDPool.
Derive GenSized for IDKWDPool.

Require Import Contracts.FromGiver.DFromGiver.Interface.
Derive Show for IDFromGiver.
Derive Shrink for IDFromGiver.
Derive GenSized for IDFromGiver.

(*PhantomType*)

#[global]
Instance iso_phantom: IsoTypes PhantomType unit.
esplit with (x2y:=fun  _ => tt) (y2x:=fun _ => PhantomPoint).
extensionality x.
unfold compose.
destruct x. reflexivity.
extensionality x.
unfold compose.
apply phantom_all.
Defined.

#[global]
Instance phantom_show: Show PhantomType .
eapply iso_show.
apply iso_phantom.
apply Showunit.
Defined.

#[global]
Instance phantom_shrink: Shrink PhantomType .
eapply iso_shrink.
apply iso_phantom.
apply Shrinkunit.
Defined.

#[global]
Instance phantom_genSized: GenSized PhantomType .
eapply iso_genSized.
apply iso_phantom.
apply GenSizedunit.
Defined.

(*MessagesAndEvents*)

#[local]
Remove Hints isoid : typeclass_instances. 
#[local]
Remove Hints iso_show : typeclass_instances.
#[local]
Remove Hints iso_shrink : typeclass_instances.
#[local]
Remove Hints iso_genSized : typeclass_instances.

(*VMState*)

#[global] 
Instance VMState_Show: Show VMStateLRecord.
refine Showxprod.
Defined.

#[global] 
Instance VMState_Shrink: Shrink VMStateLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance VMState_GenSized: GenSized VMStateLRecord. 
refine GenSizedxprod.
Defined.

Definition implb (a b: bool) := orb (negb a) b.

Definition bimplb (a b: bool) := andb  (implb a b)  (implb b a).

#[global]
Instance ge_dec: forall m n, Dec (N.ge m n).
intros.
esplit.
unfold decidable.
remember (N.ltb m n).
destruct b.
symmetry in Heqb.
apply N.ltb_lt in Heqb.
right. lia.
symmetry in Heqb.
apply N.ltb_ge in Heqb.
left. lia.
Defined.

#[global]
Instance lt_dec: forall m n, Dec (N.lt m n).
intros.
esplit.
unfold decidable.
remember (N.ltb m n).
destruct b.
symmetry in Heqb.
apply N.ltb_lt in Heqb.
left. lia.
symmetry in Heqb.
apply N.ltb_ge in Heqb.
right. lia.
Defined.

#[global]
Instance le_dec: forall m n, Dec (N.le m n).
intros.
esplit.
unfold decidable.
remember (N.leb m n).
destruct b.
symmetry in Heqb.
apply N.leb_le in Heqb.
left. lia.
symmetry in Heqb.
apply N.leb_gt in Heqb.
right. lia.
Defined.

#[global]
Instance gt_dec: forall m n, Dec (N.gt m n).
intros.
esplit.
unfold decidable.
remember (N.leb m n).
destruct b.
symmetry in Heqb.
apply N.leb_le in Heqb.
right. lia.
symmetry in Heqb.
apply N.leb_gt in Heqb.
left. lia.
Defined.

Notation ControlResult := (@ControlResultL) .
Definition isError {R b} (cr : ControlResult R b) : Prop :=
 match cr with
 | ControlValue _ _ => False
 | _ => True
 end.

#[global]
Instance isError_Dec {R b}: forall  (cr : ControlResult R b), Dec (isError cr).
intros.
esplit.
unfold decidable.
dependent destruction cr. 
now right.
all: now left.
Defined.

#[global]
Instance Dec_equiv : forall {P Q : Prop}, Dec P -> Dec Q -> Dec (P <-> Q) .
intros.
eapply Dec_conj.
Defined.

Definition uint2N {n} (x: XUBInteger n) : N.
dependent destruction x.
refine x.
Defined.

#[global] Instance prod_Dec: forall X Y (x1 x2: X) (y1 y2: Y) `{Dec (x1=x2)}`{Dec (y1=y2)}, Dec (pair x1 y1 = pair x2 y2).
intros.
esplit.
unfold decidable.
destruct H, H0.
destruct dec, dec0.
left.
congruence.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
Defined.

#[global] Instance xprod_Dec: forall X Y (x1 x2: X) (y1 y2: Y) `{Dec (x1=x2)}`{Dec (y1=y2)}, Dec (xpair x1 y1 = xpair x2 y2).
intros.
esplit.
unfold decidable.
destruct H, H0.
destruct dec, dec0.
left.
congruence.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
right.
unfold not.
intros.
inversion H.
contradiction.
Defined.

#[global]
Instance XUBIntegerEq_Dec {n} (a b: XUBInteger n): Dec (a = b).
destruct a,b.
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
Defined.

#[global]
Instance addressEq_Dec (a b: address): Dec (a = b).
destruct a,b.
esplit.
unfold decidable.
eapply prod_Dec.
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
Defined.

#[global]
Instance cellEq_Dec (a b: cell_): Dec (a = b).
esplit.
unfold decidable.
decide equality.
decide equality.
decide equality.
decide equality.
Defined.

#[global]
Instance cellBoolEq: XBoolEquable bool cell_ .
esplit.
intros.
pose proof (cellEq_Dec H H0).
destruct H1.
destruct dec.
refine true.
refine false.
Defined.



#[global]
Instance optionEq_Dec {X}`{forall (a b:X),Dec (a=b) } (a b: option X): Dec (a = b).
esplit.
unfold decidable.
decide equality.
eapply H.
Defined.



#[global] Instance VMStateEq_Dec: forall (l1 l2: VMStateLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
Defined.



Require Import FinProof.Common.
Require Import FinProof.CommonInstances.

#[global]
Instance IKWFundParticipant_booleq : XBoolEquable bool 
         Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant.
esplit.
intros.
case_eq H; intros; case_eq H0; intros.
refine (eqb x x0).
refine false. refine false. refine false. refine false. refine false. refine false.
refine true.
refine false. refine false. refine false. refine false. refine false. refine false.
refine true.
refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb c c0 ).
refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb x x4 && eqb x0 x5 && eqb x1 x6 && eqb x2 x7 && eqb x3 x8).
refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb x x2 && eqb x0 x3 && eqb x1 x4).
Defined.



#[global]
Instance IBlank_booleq : XBoolEquable bool 
         Interfaces.IBlank.IBlank.Interface.IBlank.
esplit.
intros.
case_eq X; intros; case_eq X0; intros.
refine (eqb x x5 && eqb x0 x6 && eqb x1 x7 && eqb x2 x8 && eqb x3 x9 && eqb x4 x10).
refine false. refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb a a0 && eqb x x0 ).
refine false. refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb a a0 && eqb x x1 && eqb x0 x2 ).
refine false. refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb x x1 && eqb x0 x2 ).
refine false. refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb x x1 && eqb x0 x2 ).
refine false. refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb a a0 && eqb x x2 && eqb x0 x3 && eqb x1 x4 ).
refine false. refine false. refine false. refine false. refine false. refine false. refine false.
refine (eqb x x3 && eqb x0 x4 && eqb x1 x5 && eqb x2 x6).
Defined.
 
#[global]
Instance IKWFund_booleq : XBoolEquable bool 
         Interfaces.IKWFund.IKWFund.Interface.IKWFund.
esplit.
intros.
case_eq X; intros; case_eq X0; intros.
refine (eqb x x1 && eqb x0 x2 && eqb c c0).
refine false. refine false.  
refine (eqb a a0 && eqb x x0 && eqb c c0).
Defined.


#[global]
Instance IDFromGiver_booleq : XBoolEquable bool 
         FromGiver.DFromGiver.Interface.IDFromGiver.
esplit.
intros.
case_eq H; intros; case_eq H0; intros.
refine true.
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine (eqb x x0).
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine true.
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine (eqb c c0).
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine true.
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine (eqb x x2 && eqb x0 x3 && eqb x1 x4).
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine true.
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine (eqb x x4 && eqb x0 x5 && eqb x1 x6 && eqb x2 x7 && eqb x3 x8).
refine false. refine false. refine false. refine false. refine false.  refine false.  refine false.  refine false.  refine false.
refine (eqb x x1 && eqb x0 x2).
Defined.

#[global]
Instance OutgoingMessage_booleq: forall I `{XBoolEquable bool I}, XBoolEquable bool 
         (OutgoingMessage I).
intros.
esplit.
intros.
case_eq X; intros; case_eq X0; intros.
refine true. refine false. refine false.
refine  (eqb i i1 && eqb i0 i2).
Defined.


Definition isMessageSent {I}`{XBoolEquable bool I} (m: OutgoingMessage I) (a: address) (n: N)
                         (l: XHMap address (XQueue (OutgoingMessage I))) : bool :=
  let subm := hmapFindWithDefault default a l in                      
  let maxk : option N := xHMapMaxKey subm in
  match maxk with 
    | None => false
    | Some k => 
        match hmapLookup (k-n) subm with
        | None => false
        | Some m' => eqb m m'
        end
  end. 


#[global] Instance phantom_booleq: XBoolEquable bool PhantomType := {eqb := fun _ _ => true}.

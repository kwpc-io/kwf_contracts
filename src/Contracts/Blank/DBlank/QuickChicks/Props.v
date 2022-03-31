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
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DBlank.QuickChicks.QCEnvironment.
(* Require Import UMLang.ExecGenerator. *)

Definition UinterpreterL := @Uinterpreter XBool XUInteger XMaybe XList XProd XHMap _ _ _ _ _ _
                             LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord
                             MessagesAndEventsLRecord GlobalParamsLRecord
                             OutgoingMessageParamsLRecord ledgerClass .
Arguments UinterpreterL {_} {_} {_}.

Definition ledger_prop1 (l: LedgerLRecord) := true.

(* Time QuickChick ledger_prop1.*)

Import FinProof.Common.  (*for eqb!!!*)
Require Import FinProof.CommonInstances.

(*************************************constructor*)

Definition constructor_requires (mb: uint128) ( min_summa max_summa: uint128 )  
                                (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l) in
let ult := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let q := toValue (eval_state (sRReader || quant_ || ) l) in
let fr := toValue (eval_state (sRReader || farm_rate_ || ) l) in
let kwlt := toValue (eval_state (sRReader || kwf_lock_time_ || ) l) in

let require11 := (uint2N mp) = 0            in
let require12 := (uint2N tp) <> (uint2N mp) in 
let require1  := require11 \/ require12     in
let require2  := (uint2N tb) < (uint2N mb)  in 
let require3  := (uint2N tn) >= (uint2N lt) in
let require4  := (uint2N min_summa) > (uint2N max_summa)   in
let require5  := (uint2N lt) >= (uint2N ult)               in
let require6  := (uint2N q) <= 0                           in
let require7  := ((uint2N fr) <= 0) \/ ((uint2N fr) > 100) in
let require8  := ((uint2N kwlt) <= 0) in

 require1 \/ require2 \/ require3 \/ require4 \/ require5 \/ require6 \/ require7 \/ require8.
Definition constructor_isError_prop
                           ( mb min_summa max_summa: uint128 )  
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l)
 <->  (constructor_requires mb min_summa max_summa l) .

Definition VMStateDefault : VMStateLRecord  := Eval compute in default. 

Definition constructor_isError_propb
                           ( mb min_summa max_summa: uint128 )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
constructor_isError_prop mb min_summa max_summa 
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(* Definition qcArgs := MkArgs None defNumTests defNumDiscards
                             defNumShrinks defSize true. *)

Extract Constant defNumTests => "20000".
Extract Constant defSize => "20".

(*UNCOMMENT ME*)
(* Time QuickCheck constructor_isError_propb. *) 

Definition constructor_exec_prop (mb: uint128) ( min_summa max_summa: uint128 )  
                                 (l: LedgerLRecord )  : Prop :=
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
  uint2N gs = 0 /\
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
).

Definition constructor_exec_propb (mb: uint128) ( min_summa max_summa: uint128 )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
constructor_exec_prop mb min_summa max_summa 
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
                           
(*UNCOMMENT ME*)
(* Time QuickCheck constructor_exec_propb. *)

Definition constructor_noexec_prop (mb: uint128) ( min_summa max_summa: uint128 )  
                                   (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (constructor_ (KWMessages_ι_BLANK_MIN_BALANCE_:=mb) min_summa max_summa)) l in

constructor_requires mb min_summa max_summa l -> 
Ledger_MainState l = Ledger_MainState l'.

Definition constructor_noexec_propb (mb: uint128) ( min_summa max_summa: uint128 )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
constructor_noexec_prop mb min_summa max_summa 
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
                           

(* #[local]
Existing Instance ContractEq_Dec.
#[local]
Remove Hints prod_Dec : typeclass_instances.
#[local]
Remove Hints xprod_Dec : typeclass_instances. *)

(*UNCOMMENT ME*)
(* Time QuickCheck constructor_noexec_propb. *)

(*************************************setFromGiverCode*)

Definition setFromGiverCodeHash_requires (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )  
                                     (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l)  in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l)  in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l)     in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l)     in
let ccf := toValue (eval_state (sRReader || can_change_fromgiver_code_ || ) l) in

let require11 := (uint2N mp) = 0 in
let require12 := (uint2N tp) <> (uint2N mp) in 
let require1 := require11 \/ require12 in
let require2 := ccf = false in
let require3 :=  (uint2N tb) < (uint2N eb) in 
let require4 :=  (uint2N tn) >= (uint2N lt) in

 require1 \/ require2 \/ require3 \/ require4 .

(* Check setFromGiverCode. *)
Definition setFromGiverCodeHash_isError_prop
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )  
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l)
 <-> (setFromGiverCodeHash_requires eb code_hash code_depth l) .

Definition setFromGiverCodeHash_isError_propb
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
setFromGiverCodeHash_isError_prop eb code_hash code_depth
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setFromGiverCodeHash_isError_propb. *)  

Definition setFromGiverCodeHash_exec_prop (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )   
                                      (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l in
let fgch := toValue (eval_state (sRReader || fromgiver_code_hash_ || ) l')  in
let fgcd := toValue (eval_state (sRReader || fromgiver_code_depth_ || ) l') in

(~ (setFromGiverCodeHash_requires eb code_hash code_depth l)) -> 
(
  uint2N fgch = uint2N code_hash /\
  uint2N fgcd = uint2N code_depth /\
  VMState_ι_accepted (Ledger_VMState l') = true
).

Definition setFromGiverCodeHash_exec_propb
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
setFromGiverCodeHash_exec_prop eb code_hash code_depth
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setFromGiverCodeHash_exec_propb. *)

Definition setFromGiverCodeHash_noexec_prop (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )   
                                      (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFromGiverCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l in
setFromGiverCodeHash_requires eb code_hash code_depth l -> 
 Ledger_MainState l = Ledger_MainState l'.

Definition setFromGiverCodeHash_noexec_propb
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
setFromGiverCodeHash_noexec_prop eb code_hash code_depth
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setFromGiverCodeHash_noexec_propb. *)

(*************************************setKWDPoolCode*)

Definition setKWDPoolCode_requires (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )  
                                     (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader  || msg_pubkey ()  || ) l)     in
let tp := toValue (eval_state (sRReader  || tvm_pubkey ()  || ) l)     in
let tb := toValue (eval_state (sRReader  || tvm_balance () || ) l)    in
let tn := toValue (eval_state (sRReader  || tvm_now ()     || ) l)        in
let lt := toValue (eval_state (sRReader  || lock_time_     || ) l)        in
let ccf := toValue (eval_state (sRReader || can_change_kwdpool_code_ || ) l) in

let require11 := (uint2N mp) = 0            in
let require12 := (uint2N tp) <> (uint2N mp) in
let require1  := require11 \/ require12     in
let require2  := ccf = false                in
let require3  := (uint2N tb) < (uint2N eb)  in 
let require4  := (uint2N tn) >= (uint2N lt) in

 require1 \/ require2 \/ require3 \/ require4 .

Definition setKWDPoolCode_isError_prop
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )  
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (setKWDPoolCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l)
 <-> (setKWDPoolCode_requires eb code_hash code_depth l) .

Definition setKWDPoolCode_isError_propb
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
setKWDPoolCode_isError_prop eb code_hash code_depth
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setKWDPoolCode_isError_propb. *)

Definition setKWDPoolCode_exec_prop (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )   
                                      (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setKWDPoolCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l in
let kwdch := toValue (eval_state (sRReader || kwdpool_code_hash_ || ) l')  in
let kwdcd := toValue (eval_state (sRReader || kwdpool_code_depth_ || ) l') in

(~ (setKWDPoolCode_requires eb code_hash code_depth l)) -> 
(
  uint2N kwdch = uint2N code_hash /\
  uint2N kwdcd = uint2N code_depth /\
  VMState_ι_accepted (Ledger_VMState l') = true
).

Definition setKWDPoolCode_exec_propb
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
setKWDPoolCode_exec_prop eb code_hash code_depth
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setKWDPoolCode_exec_propb. *)

Definition setKWDPoolCode_noexec_prop (eb: uint128) ( code_hash: uint256) (code_depth: uint16 )   
                                      (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setKWDPoolCodeHash_ (KWMessages_ι_EPSILON_BALANCE_:=eb) code_hash code_depth)) l in
setKWDPoolCode_requires eb code_hash code_depth l -> 
 Ledger_MainState l = Ledger_MainState l'.

Definition setKWDPoolCode_noexec_propb
                           (eb: uint128) ( code_hash: uint256) (code_depth: uint16 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
setKWDPoolCode_noexec_prop eb code_hash code_depth
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setKWDPoolCode_noexec_propb. *)

(*************************************isFundReady*)

Definition isFundReady_requires (vbf :uint16) (pkin : uint256 ) (nonce : uint256)
                                (l: LedgerLRecord )  : Prop :=
let ci := isError (eval_state (UinterpreterL (check_investor pkin nonce _ _ {{ return_ #{PhantomPoint} }} )) l) in
let require1 := ci in
  require1.
Definition isFundReady_isError_prop (vbf :uint16) (pkin : uint256 ) (nonce : uint256)   
                                    ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (isFundReady_  (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) pkin nonce)) l)
 <-> (isFundReady_requires vbf pkin nonce l) .

Definition isFundReady_isError_propb (vbf :uint16)
                           ( pkin : uint256 ) ( nonce : uint256 )   
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
isFundReady_isError_prop vbf pkin nonce
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck isFundReady_isError_propb. *)

Definition isFundReady_exec_prop (vbf :uint16)
                                (pkin : uint256 ) 
                                 (nonce : uint256)   
                                 (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (isFundReady_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) pkin nonce)) l in
let cck := toValue (eval_state (sRReader || can_change_kwdpool_code_ || ) l') in
let lt  := toValue (eval_state (sRReader || lock_time_ || ) l) in
let ult := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let q   := toValue (eval_state (sRReader || quant_ || ) l) in
let fr  := toValue (eval_state (sRReader || farm_rate_ || ) l) in
let klt := toValue (eval_state (sRReader || kwf_lock_time_ || ) l) in

let mm := toValue (eval_state (sRReader IKWFundParticipantPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || int_sender () || ) l) in
let params:InternalMessageParamsLRecord := (Build_XUBInteger 0, (true, MSG_VALUE_BUT_FEE)) in
let func: Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant :=
          Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.Iinitialize lt ult q fr klt in
let message := OutgoingInternalMessage params func in
let ms := isMessageSent message a 0 mm             in

(~ (isFundReady_requires vbf pkin nonce l)) -> 
(
  cck = false /\ 
  ms = true
).

Definition MessagesAndEventsDefault : MessagesAndEventsLRecord:= Eval compute in default.

Definition isFundReady_exec_propb (vbf :uint16)
                           ( pkin : uint256 ) (nonce : uint256) 
                           ( l: ContractLRecord ) (me: MessagesAndEventsLRecord)
                           ( pk: uint256  )
                           ( mpk: uint256 ) 
                           ( mn : uint32 )
                           ( ms: address  )
                           ( mv: uint128  )
                           ( tb: uint128  )
                           ( kwdpm : mapping address (queue (OutgoingMessage Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant))) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IKWFundParticipant := kwdpm $$} in
                       
isFundReady_exec_prop vbf pkin nonce
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me0 $$} ? .

(*UNCOMMENT ME*)
Extract Constant defNumTests => "10000".
(* Time QuickCheck isFundReady_exec_propb. *)

(*************************************notifyLeft*)

Definition notifyLeft_requires (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                                (l: LedgerLRecord )  : Prop :=
let ci := isError (eval_state (UinterpreterL (check_investor pkin nonce _ _ {{ return_ #{PhantomPoint} }} )) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l)     in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l)     in

let require1 := ci in
let require2  := (uint2N tb) < (uint2N eb) in 
let require3 := (uint2N tn) >= (uint2N lt) in
  require1 \/ require2 \/ require3.

  Definition notifyLeft_isError_prop (vbf :uint16)
                           (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                           (balance : uint128 ) (adj_balance : uint128)
                           (l: LedgerLRecord ) : Prop :=
isError (eval_state (UinterpreterL (notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l)
 <-> (notifyLeft_requires eb pkin nonce l).

Definition notifyLeft_isError_propb (vbf :uint16)
                           (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                           (balance : uint128 ) (adj_balance : uint128)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
notifyLeft_isError_prop vbf eb pkin nonce balance adj_balance
      {$$ 
      {$$ LedgerDefault with Ledger_MainState := l $$}
                        with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck notifyLeft_isError_propb. *)

Definition notifyLeft_exec_prop (vbf :uint16) (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                                (balance : uint128 ) (adj_balance : uint128)  
                                (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l in

let ias := toValue (eval_state (sRReader || investors_adj_summa_ || ) l) in
let iss  := toValue (eval_state (sRReader || investors_summa_ || ) l) in
let ns := toValue (eval_state (sRReader || num_investors_sent_ || ) l) in
let sender   := toValue (eval_state (sRReader || int_sender() || ) l) in

let ias' := toValue (eval_state (sRReader || investors_adj_summa_ || ) l') in
let iss'  := toValue (eval_state (sRReader || investors_summa_ || ) l') in
let ns' := toValue (eval_state (sRReader || num_investors_sent_ || ) l') in

let mm : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || int_sender () || ) l) in
let params : InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, vbf)) in
let message := EmptyMessage PhantomType params in 
let ms := isMessageSent message a 0 mm in

(~ (notifyLeft_requires eb pkin nonce l)) -> 
(
   VMState_ι_accepted (Ledger_VMState l') = true /\
   uint2N ias' =  (uint2N ias) + (uint2N adj_balance) /\
   uint2N iss' =  (uint2N iss) + (uint2N balance) /\
   uint2N ns' = (uint2N ns) + 1 /\
   ms
).

Definition notifyLeft_exec_propb (vbf :uint16)
                           (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                           (balance : uint128 ) (adj_balance : uint128)  
                           ( l: ContractLRecord ) (me: MessagesAndEventsLRecord)
                           ( pk: uint256  )
                           ( mpk: uint256 ) 
                           ( mn : uint32 )
                           ( ms: address  )
                           ( mv: uint128  )
                           ( tb: uint128  ) 
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_Default := dm $$} in
                       
notifyLeft_exec_prop vbf eb pkin nonce balance adj_balance
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me0 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck notifyLeft_exec_propb. *)

(*balance > 0, balance = quant ???*)
(*farm_rate = 0?*)
(*make Messages default but the needed projection as VMState!*)
(*quant*farm_rate/100 > 0*)

Definition notifyLeft_noexec_prop (vbf :uint16) (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                                  (balance : uint128 ) (adj_balance : uint128)   
                                  (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyLeft_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) pkin nonce balance adj_balance)) l in
notifyLeft_requires eb pkin nonce l -> 
 Ledger_MainState l = Ledger_MainState l'.

Definition notifyLeft_noexec_propb (vbf :uint16)
                           (eb: uint128) (pkin : uint256 ) (nonce : uint256)
                           (balance : uint128 ) (adj_balance : uint128) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
notifyLeft_noexec_prop vbf eb pkin nonce balance adj_balance
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck notifyLeft_noexec_propb. *)

(*************************************deployFromGiver*)

(*change giver!=0 to address ↑ address or isStdZero*)
(*change  tvm_balance() >= 2 EB to smth more appropriate*)

Definition deployFromGiver_requires (fgmb eb: uint128)
                                    (code : cell_) 
                                    (giver : address )   
                                    (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l) in
let fgch := toValue (eval_state (sRReader || fromgiver_code_hash_ || ) l) in

let require11 :=  (uint2N mp) = 0             in
let require12 :=  (uint2N tp) <> (uint2N mp)  in 
let require1  :=  require11 \/ require12      in
let require2  :=  (uint2N tn) >= (uint2N lt)  in 
let require3  :=  giver = default in 
let require4  :=  tvm_hash_cell code <> fgch in  
let require5  :=  (uint2N tb) < (uint2N fgmb) + 2 * (uint2N eb) in 

 require1 \/ require2  \/ require3  \/ require4 \/ require5   .

Definition deployFromGiver_isError_prop
                           (fgmb eb: uint128)
                           (code : cell_) 
                           (giver : address)
                           (nonce : uint256)  
                           (l: LedgerLRecord)  : Prop :=
isError (eval_state (UinterpreterL (deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l)
 <->  (deployFromGiver_requires fgmb eb code giver l) .
Definition deployFromGiver_isError_propb
                           (fgmb eb: uint128)
                           (code : cell_) 
                           (giver : address)
                           (nonce : uint256)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
deployFromGiver_isError_prop fgmb eb code giver nonce
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

Extract Constant defNumTests => "10000".
Extract Constant defSize => "7".

(*UNCOMMENT ME*)
(* Time QuickCheck deployFromGiver_isError_propb. *)

Definition deployFromGiver_exec_prop (fgmb eb: uint128)
                                      (code : cell_) 
                                      (giver : address)
                                      (nonce : uint256)   
                                      (l: LedgerLRecord )  : Prop :=
let lt := toValue (eval_state (sRReader || lock_time_ || ) l) in
let ult := toValue (eval_state (sRReader || unlock_time_ || ) l) in

let l' := exec_state (UinterpreterL (deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l in

let dataCell := toValue (eval_state (UinterpreterL (buildFromGiverDataInitCell_ giver nonce)) l) in 
let stateInit := tvmFunc.tvm_buildStateInit code dataCell (Build_XUBInteger 0) in
let di:DeployInitLRecord := ( xIntPlus fgmb eb , stateInit) in 
let constr : FromGiver.DFromGiver.Interface.IDFromGiver := FromGiver.DFromGiver.Interface._Iconstructor lt ult in 
let fgaddr := toValue (eval_state (UinterpreterL (tvmFunc.tvm_newContract {{DFromGiverPtr}} di constr)) l) in 

let mm : XHMap address (XQueue (OutgoingMessage FromGiver.DFromGiver.Interface.IDFromGiver)) := toValue (eval_state (sRReader IDFromGiverPtr_messages_right ) l') in 
let params : InternalMessageParamsLRecord := (xIntPlus fgmb eb, (false, Build_XUBInteger 0)) in 
let message := OutgoingInternalMessage params constr in 
let ms := isMessageSent message fgaddr 0 mm in 

(~ (deployFromGiver_requires fgmb eb code giver l )) -> 
(
  VMState_ι_accepted (Ledger_VMState l') = true /\
  Ledger_MainState l = Ledger_MainState l' /\
  ms
).

Definition deployFromGiver_exec_propb (fgmb eb: uint128)
                                      (code : cell_) 
                                      (giver : address)
                                      (nonce : uint256)  
                                      ( l: ContractLRecord )
                                      ( pk: uint256 )
                                      ( mpk: uint256) 
                                      ( mn : uint32 )
                                      ( ms: address )
                                      ( mv: uint128 )
                                      ( tb: uint128 ) 
                                      ( fgm : mapping address (queue (OutgoingMessage FromGiver.DFromGiver.Interface.IDFromGiver))) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IDFromGiver := fgm $$} in

                       
deployFromGiver_exec_prop fgmb eb code giver nonce 
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me0 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck deployFromGiver_exec_propb. *)

Definition deployFromGiver_noexec_prop 
                                  (fgmb eb: uint128)
                                  (code : cell_) 
                                  (giver : address)
                                  (nonce : uint256) 
                                  (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (deployFromGiver_ (KWMessages_ι_FG_MIN_BALANCE_:=fgmb) (KWMessages_ι_EPSILON_BALANCE_:=eb) code giver nonce)) l in
deployFromGiver_requires fgmb eb code giver l -> 
(* actually the function function doesn't change state *)
 Ledger_MainState l = Ledger_MainState l'.

Definition deployFromGiver_noexec_propb
                            (fgmb eb: uint128)
                            (code : cell_) 
                            (giver : address)
                            (nonce : uint256)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
deployFromGiver_noexec_prop fgmb eb code giver nonce
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck deployFromGiver_noexec_propb. *)

(*************************************acknowledgeDeploy*)

Definition acknowledgeDeploy_requires (giver : address) (nonce : uint256)
                                      (l: LedgerLRecord )  : Prop :=
let cg := isError (eval_state (UinterpreterL (check_giver giver nonce _ _ {{ return_ #{PhantomPoint} }} )) l) in
let require1 := cg in
  require1 .

Definition acknowledgeDeploy_isError_prop
                           (giver : address) (nonce : uint256)  
                           (l: LedgerLRecord)  : Prop :=
isError (eval_state (UinterpreterL (acknowledgeDeploy_ giver nonce)) l)
 <->  (acknowledgeDeploy_requires giver nonce l) .

Definition acknowledgeDeploy_isError_propb
                           (giver : address) (nonce : uint256)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeDeploy_isError_prop giver nonce
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeDeploy_isError_propb. *)

Definition acknowledgeDeploy_exec_prop (giver : address) (nonce : uint256)   
                                       (l: LedgerLRecord )  : Prop :=
let ni := toValue (eval_state (sRReader || num_investors_sent_ || ) l) in
(* let ccfg := toValue (eval_state (sRReader || can_change_fromgiver_code_ || ) l) in *)

let l' := exec_state (UinterpreterL (acknowledgeDeploy_ giver nonce)) l in

let ni' := toValue (eval_state (sRReader || num_investors_sent_ || ) l') in
let ccfg' := toValue (eval_state (sRReader || can_change_fromgiver_code_ || ) l') in

(~ (acknowledgeDeploy_requires giver nonce l )) -> 
(
  VMState_ι_accepted (Ledger_VMState l') = true /\
  uint2N ni' = uint2N ni + 1 /\
  ccfg' = false
).

Definition acknowledgeDeploy_exec_propb
                           (giver : address) (nonce : uint256)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeDeploy_exec_prop giver nonce
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeDeploy_exec_propb. *)

Definition acknowledgeDeploy_noexec_prop (giver : address) (nonce : uint256)   
                                       (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeDeploy_ giver nonce)) l in
(acknowledgeDeploy_requires giver nonce l ) -> 
  Ledger_MainState l = Ledger_MainState l'.

Definition acknowledgeDeploy_noexec_propb
                           (giver : address) (nonce : uint256)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeDeploy_noexec_prop giver nonce
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeDeploy_noexec_propb. *) 

(*************************************notifyRight*)

Definition notifyRight_requires (eb: uint128) (giver : address ) (nonce : uint256)
                                (l: LedgerLRecord )  : Prop :=
let cg := isError (eval_state (UinterpreterL (check_giver giver nonce _ _ {{ return_ #{PhantomPoint} }} )) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l)     in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l)     in

let require1 := cg in
let require2  := (uint2N tb) < (uint2N eb) in 
let require3 := (uint2N tn) >= (uint2N lt) in
  require1 \/ require2 \/ require3.

  Definition notifyRight_isError_prop (vbf :uint16)
                           (eb: uint128) (giver : address ) (nonce : uint256)
                           (balance : uint128 ) (income : uint128)
                           (l: LedgerLRecord ) : Prop :=
isError (eval_state (UinterpreterL (notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) giver nonce balance income)) l)
 <-> (notifyRight_requires eb giver nonce l).

Definition notifyRight_isError_propb (vbf :uint16)
                           (eb: uint128) (giver : address ) (nonce : uint256)
                           (balance : uint128 ) (income : uint128)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
notifyRight_isError_prop vbf eb giver nonce balance income
      {$$ 
      {$$ LedgerDefault with Ledger_MainState := l $$}
                        with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck notifyRight_isError_propb. *)

Definition notifyRight_exec_prop (vbf :uint16) (eb: uint128) (giver : address ) (nonce : uint256)
                                 (balance : uint128 ) (income : uint128)
                                 (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) giver nonce balance income)) l in

let gs := toValue (eval_state (sRReader || givers_summa_ || ) l) in
let sender   := toValue (eval_state (sRReader || int_sender() || ) l) in

let gs' := toValue (eval_state (sRReader || givers_summa_ || ) l') in

let mm : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || int_sender () || ) l) in
let params : InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, vbf)) in
let message := EmptyMessage PhantomType params in 
let ms := isMessageSent message a 0 mm in

(~ (notifyRight_requires eb giver nonce l)) -> 
(
   VMState_ι_accepted (Ledger_VMState l') = true /\
   uint2N gs' =  (uint2N gs) + (uint2N income) /\
   ms
).

Definition notifyRight_exec_propb (vbf :uint16)
                           (eb: uint128) (giver : address ) (nonce : uint256)
                           (balance : uint128 ) (income : uint128)  
                           ( l: ContractLRecord ) (me: MessagesAndEventsLRecord)
                           ( pk: uint256  )
                           ( mpk: uint256 ) 
                           ( mn : uint32 )
                           ( ms: address  )
                           ( mv: uint128  )
                           ( tb: uint128  ) 
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_Default := dm $$} in
                       
notifyRight_exec_prop vbf eb giver nonce balance income
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me0 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck notifyRight_exec_propb. *)

Definition notifyRight_noexec_prop (vbf :uint16) (eb: uint128) (giver : address ) (nonce : uint256)
                                   (balance : uint128 ) (income : uint128)   
                                   (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyRight_ (KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_ :=vbf) (KWMessages_ι_EPSILON_BALANCE_:=eb) giver nonce balance income)) l in
notifyRight_requires eb giver nonce l -> 
 Ledger_MainState l = Ledger_MainState l' /\
 Ledger_MessagesState l = Ledger_MessagesState l'.

Definition notifyRight_noexec_propb (vbf :uint16)
                           (eb: uint128) (giver : address ) (nonce : uint256)
                           (balance : uint128 ) (income : uint128) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                           ( me: MessagesAndEventsLRecord)  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
notifyRight_noexec_prop vbf eb giver nonce balance income
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$}
                          with Ledger_MessagesState := me $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck notifyRight_noexec_propb. *)

(*************************************acknowledgeFinalizeRight*)

Definition acknowledgeFinalizeRight_requires (giver : address) (nonce : uint256) (dead_giver :  XBool  )
                                      (l: LedgerLRecord )  : Prop :=
let cg := isError (eval_state (UinterpreterL (check_giver giver nonce _ _ {{ return_ #{PhantomPoint} }} )) l) in
let require1 := cg in
  require1 .
Check acknowledgeFinalizeRight_.
Definition acknowledgeFinalizeRight_isError_prop
                           (giver : address) (nonce : uint256)  (dead_giver :  XBool  )
                           (l: LedgerLRecord)  : Prop :=
isError (eval_state (UinterpreterL (acknowledgeFinalizeRight_ giver nonce dead_giver )) l) 
 <->  (acknowledgeFinalizeRight_requires giver nonce dead_giver l) .

Definition acknowledgeFinalizeRight_isError_propb
                           (giver : address) (nonce : uint256) (dead_giver :  XBool  ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeFinalizeRight_isError_prop giver nonce dead_giver
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeFinalizeRight_isError_propb. *)

Definition acknowledgeFinalizeRight_exec_prop (giver : address) (nonce : uint256)  (dead_giver :  XBool  ) 
                                              (l: LedgerLRecord )  : Prop :=
let ni := toValue (eval_state (sRReader || num_investors_received_ || ) l) in

let l' := exec_state (UinterpreterL (acknowledgeFinalizeRight_ giver nonce dead_giver)) l in

let ni' := toValue (eval_state (sRReader || num_investors_received_ || ) l') in

(~ (acknowledgeFinalizeRight_requires giver nonce dead_giver l )) -> 
(
  VMState_ι_accepted (Ledger_VMState l') = true /\
  uint2N ni' = uint2N ni + 1
).

Definition acknowledgeFinalizeRight_exec_propb
                           (giver : address) (nonce : uint256)  (dead_giver :  XBool  )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeFinalizeRight_exec_prop giver nonce dead_giver
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeFinalizeRight_exec_propb. *)

Definition acknowledgeFinalizeRight_noexec_prop (giver : address) (nonce : uint256)   (dead_giver :  XBool  )
                                       (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeFinalizeRight_ giver nonce dead_giver)) l in
(acknowledgeFinalizeRight_requires giver nonce dead_giver l ) -> 
  Ledger_MainState l = Ledger_MainState l' /\
  Ledger_MessagesState l = Ledger_MessagesState l'.

Definition acknowledgeFinalizeRight_noexec_propb
                           ( giver : address ) ( nonce : uint256 )  (dead_giver :  XBool  )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )
                           ( me: MessagesAndEventsLRecord )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in

acknowledgeFinalizeRight_noexec_prop giver nonce dead_giver
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeFinalizeRight_noexec_propb. *)

(*************************************acknowledgeFinalizeLeft*)

Definition acknowledgeFinalizeLeft_requires (pkin : uint256 ) (nonce : uint256)
                                      (l: LedgerLRecord )  : Prop :=
let ci := isError (eval_state (UinterpreterL (check_investor pkin nonce _ _ {{ return_ #{PhantomPoint} }} )) l) in
let require1 := ci in
  require1 .

Definition acknowledgeFinalizeLeft_isError_prop
                           (pkin : uint256 ) (nonce : uint256)
                           (l: LedgerLRecord)  : Prop :=
isError (eval_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l)
 <->  (acknowledgeFinalizeLeft_requires pkin nonce l) .

Definition acknowledgeFinalizeLeft_isError_propb
                           (pkin : uint256 ) (nonce : uint256)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeFinalizeLeft_isError_prop pkin nonce
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeFinalizeLeft_isError_propb. *)

Definition acknowledgeFinalizeLeft_exec_prop (pkin : uint256 ) (nonce : uint256)
                                             (l: LedgerLRecord )  : Prop :=
let ni := toValue (eval_state (sRReader || num_investors_received_ || ) l) in

let l' := exec_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l in

let ni' := toValue (eval_state (sRReader || num_investors_received_ || ) l') in

(~ (acknowledgeFinalizeLeft_requires pkin nonce l )) -> 
(
  VMState_ι_accepted (Ledger_VMState l') = true /\
  uint2N ni' = uint2N ni + 1
).

Definition acknowledgeFinalizeLeft_exec_propb
                           (pkin : uint256 ) (nonce : uint256)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
acknowledgeFinalizeLeft_exec_prop pkin nonce
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeFinalizeLeft_exec_propb. *)

Definition acknowledgeFinalizeLeft_noexec_prop (pkin : uint256 ) (nonce : uint256)
                                               (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeFinalizeLeft_ pkin nonce)) l in
(acknowledgeFinalizeLeft_requires pkin nonce l ) -> 
  Ledger_MainState l = Ledger_MainState l' /\
  Ledger_MessagesState l = Ledger_MessagesState l'.

Definition acknowledgeFinalizeLeft_noexec_propb
                           (pkin : uint256 ) (nonce : uint256)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )
                           ( me: MessagesAndEventsLRecord )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in

acknowledgeFinalizeLeft_noexec_prop pkin nonce
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck acknowledgeFinalizeLeft_noexec_propb. *)


(*************************************finalize*)

Definition finalize_requires (eb: uint128) (gpm: uint128) 
                             (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in                             
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l)     in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l)     in
let ult := toValue (eval_state (sRReader || unlock_time_ || ) l)     in
let nis := toValue (eval_state (sRReader || num_investors_sent_ || ) l)  in
let nir := toValue (eval_state (sRReader || num_investors_received_ || ) l)  in
let iss := toValue (eval_state (sRReader || investors_summa_ || ) l)  in
let gs := toValue (eval_state (sRReader || givers_summa_ || ) l)  in
let ms := toValue (eval_state (sRReader || min_summa_ || ) l)  in
let mss := if (ltb iss gs) then iss else gs in

let require11 := (uint2N mp) = 0            in
let require12 := (uint2N tp) <> (uint2N mp) in 
let require1 := require11 \/ require12     in
let require2 := (uint2N tn) < (uint2N lt) \/ (uint2N tn) > (uint2N ult) in
let require3 := (uint2N tb) < (uint2N eb) + (uint2N gpm)  in 
(* let require4 := (uint2N mss) < (uint2N ms) in
 *)let require5 := (uint2N nis) <= (uint2N nir) in

  require1 \/ require2 \/ require3 (* \/ require4 *) \/ require5.
Check finalize_.
Definition finalize_isError_prop 
                           (eb: uint128) (gpm: uint128)
                           (force_giveup :  XBool  ) 
                           (addr: address)
                           (l: LedgerLRecord ) : Prop :=
isError (eval_state (UinterpreterL (finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb) (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l)
 <-> (finalize_requires eb gpm l).

Definition finalize_isError_propb
                           (eb: uint128) (gpm: uint128) 
                           (force_giveup :  XBool  )
                           (addr: address)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
                       
finalize_isError_prop eb gpm force_giveup addr
      {$$ 
      {$$ LedgerDefault with Ledger_MainState := l $$}
                        with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck finalize_isError_propb. *)
Definition finalize_exec_prop (eb: uint128) (gpm: uint128) 
(force_giveup :  XBool  ) (addr: address)
                              (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb) (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l in

let gs := toValue (eval_state (sRReader || givers_summa_ || ) l) in
let ias := toValue (eval_state (sRReader || investors_adj_summa_ || ) l) in
let investors_summa := toValue (eval_state (sRReader || investors_summa_ || ) l) in
let ms := toValue (eval_state (sRReader || min_summa_ || ) l) in
let giveup := ( orb (N.ltb (N.min (uint2N investors_summa) (uint2N gs)) (uint2N ms))%N force_giveup ) in

let mm := toValue (eval_state (sRReader IKWFundParticipantPtr_messages_right ) l') in
let params:InternalMessageParamsLRecord := (gpm, (true, Build_XUBInteger 1)) in
let func: Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant :=
          Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.InotifyParticipant giveup ias gs in
let message := OutgoingInternalMessage params func in
let ms := isMessageSent message addr 0 mm in

(~ (finalize_requires eb gpm l)) -> 
(
   Ledger_MainState l = Ledger_MainState l' /\
   VMState_ι_accepted (Ledger_VMState l') = true /\
   ms
).

Definition finalize_exec_propb
                           (eb: uint128) (gpm: uint128) 
                           (force_giveup :  XBool  )
                           (addr: address)  
                           ( l: ContractLRecord ) (me: MessagesAndEventsLRecord)
                           ( pk: uint256  )
                           ( mpk: uint256 ) 
                           ( mn : uint32 )
                           ( ms: address  )
                           ( mv: uint128  )
                           ( tb: uint128  ) 
                           ( dm : mapping address (queue (OutgoingMessage Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant))) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IKWFundParticipant := dm $$} in
                       
finalize_exec_prop eb gpm force_giveup addr
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me0 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck finalize_exec_propb. *)

Definition finalize_noexec_prop (eb: uint128) (gpm: uint128) 
(force_giveup :  XBool  )
                                (addr: address)  
                                (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb) (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l in
finalize_requires eb gpm  l -> 
 Ledger_MainState l = Ledger_MainState l' /\
 Ledger_MessagesState l = Ledger_MessagesState l'.

Definition finalize_noexec_propb
                           (eb: uint128) (gpm: uint128)
                           (force_giveup :  XBool  ) 
                           (addr: address)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                           ( me: MessagesAndEventsLRecord)  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
finalize_noexec_prop eb gpm force_giveup addr
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$}
                          with Ledger_MessagesState := me $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck finalize_noexec_propb.  *)                         

Definition finalize_noexec_contract_prop (eb: uint128) (gpm: uint128) 
(force_giveup :  XBool  )  (addr: address)  
                                (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (finalize_ (KWMessages_ι_EPSILON_BALANCE_:=eb) (KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_:=gpm) force_giveup addr)) l in
 Ledger_MainState l = Ledger_MainState l' .

Definition finalize_noexec_contract_propb
                           (eb: uint128) (gpm: uint128) 
                           (force_giveup :  XBool  ) (addr: address)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                             : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
finalize_noexec_contract_prop eb gpm force_giveup addr
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .


(*UNCOMMENT ME*)
(* Time QuickCheck finalize_noexec_contract_propb. *)

(* change a little logic on nir < nis, in finalize and setFundCode *)

(*************************************setFundCode*)

Definition setFundCode_requires (rb: uint128) (tffc : uint32)
                                (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l) in
let ult := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let nis := toValue (eval_state (sRReader || num_investors_sent_ || ) l)  in
let nir := toValue (eval_state (sRReader || num_investors_received_ || ) l)  in

let require11 := (uint2N mp) = 0            in
let require12 := (uint2N tp) <> (uint2N mp) in 
let require1  := require11 \/ require12     in
let require2  := nis <> nir  in
let require3  := (uint2N tn) < (uint2N lt) \/ (uint2N tn) > (uint2N ult) in
let require4  := (uint2N tb) < (uint2N rb)  in 

 require1 \/ require2 \/ require3 \/ require4 .
Definition setFundCode_isError_prop
                           ( rb: uint128 ) (tffc : uint32) (code : cell_ ) 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (setFundCode_ (KWMessages_ι_RESPAWN_BALANCE_:=rb) (KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_ := tffc) code)) l)
 <->  (setFundCode_requires rb tffc l) .

Definition setFundCode_isError_propb
                           ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
setFundCode_isError_prop rb tffc code
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck setFundCode_isError_propb.  *)

Definition setFundCode_exec_prop  ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                                  (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFundCode_ (KWMessages_ι_RESPAWN_BALANCE_:=rb) (KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_ := tffc) code)) l in

let cd := toValue (eval_state (sRReader || tvm_code () || ) l') in
let ccd := toValue (eval_state (sRReader || tvm_currentCode () || ) l') in

(~ (setFundCode_requires rb tffc l)) -> 
(
  cd = code /\
  ccd = code /\
  VMState_ι_accepted (Ledger_VMState l') = true
).

Definition setFundCode_exec_propb ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
setFundCode_exec_prop rb tffc code 
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
                           
(*UNCOMMENT ME*)
(* Time QuickCheck setFundCode_exec_propb. *)

Definition setFundCode_noexec_prop ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                                   (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFundCode_ (KWMessages_ι_RESPAWN_BALANCE_:=rb) (KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_ := tffc) code )) l in
setFundCode_requires rb tffc l -> 
Ledger_MainState l = Ledger_MainState l' /\
Ledger_VMState l = Ledger_VMState l'.

Definition setFundCode_noexec_propb  ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
setFundCode_noexec_prop rb tffc code
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
                          

(*UNCOMMENT ME*)
(* Time QuickCheck setFundCode_noexec_propb. *)


Definition setFundCode_contract_noexec_prop ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                                   (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFundCode_ (KWMessages_ι_RESPAWN_BALANCE_:=rb) (KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_ := tffc) code )) l in
Ledger_MainState l = Ledger_MainState l'.

Definition setFundCode_contract_noexec_propb  ( rb: uint128 ) (tffc : uint32) (code : cell_ )  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$}         in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}     in
                       
setFundCode_noexec_prop rb tffc code
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
                          
(*UNCOMMENT ME*)
(* Time QuickCheck setFundCode_contract_noexec_propb. *)

(*************************************killBlank*)

Definition killBlank_requires (eb: uint128) (address_to: address)
                              (l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l)     in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l)     in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l)    in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l)        in
let ult := toValue (eval_state (sRReader || unlock_time_ || ) l)     in
let myaddr := toValue (eval_state (sRReader || tvm_myaddr () || ) l)     in

let require11 := (uint2N mp) = 0            in
let require12 := (uint2N tp) <> (uint2N mp) in 
let require1 := require11 \/ require12      in
let require2 := address_to = myaddr         in
let require3 := (uint2N tn) <= (uint2N ult) in
let require4 := (uint2N tb) < (uint2N eb)   in

  require1 \/ require2 \/ require3 \/ require4 .

Definition killBlank_isError_prop 
                           (eb: uint128) (address_to: address)
                           (l: LedgerLRecord ) : Prop :=
isError (eval_state (UinterpreterL (killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l)
 <-> (killBlank_requires eb address_to l).

Definition killBlank_isError_propb
                           ( eb: uint128 ) ( address_to: address )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( myaddr: address )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in
let v6 := {$$ v5 with VMState_ι_address := myaddr $$}            in
                       
killBlank_isError_prop eb address_to
      {$$ 
      {$$ LedgerDefault with Ledger_MainState := l $$}
                        with Ledger_VMState   := v6  $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck killBlank_isError_propb. *)

(* refine {{ tvm_transfer ( #{ a } , β 0 , FALSE , #{SEND_ALL_GAS} \\ 
												  #{SENDER_WANTS_TO_PAY_FEES_SEPARATELY} \\ 
												  #{DELETE_ME_IF_I_AM_EMPTY} \\
												  #{IGNORE_ACTION_ERRORS} ) ; {_: _ _ false} ; {_} }}.
 *)

Definition killBlank_exec_prop ( eb: uint128 ) ( address_to: address ) 
                               (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l in

let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
let gs := toValue (eval_state (sRReader || givers_summa_ || ) l) in
let ias := toValue (eval_state (sRReader || investors_adj_summa_ || ) l) in

let mm := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let params:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message := EmptyMessage _ params in
let ms := isMessageSent message address_to 0 mm in

(~ (killBlank_requires eb address_to l)) -> 
(
   Ledger_MainState l = Ledger_MainState l' /\
   VMState_ι_accepted (Ledger_VMState l') = true /\
   VMState_ι_isTVMExited (Ledger_VMState l') = true /\
   ms
).

Definition killBlank_exec_propb
                           (eb: uint128) 
                           (address_to: address)  
                           ( l: ContractLRecord ) (me: MessagesAndEventsLRecord)
                           ( pk: uint256  )
                           ( mpk: uint256 ) 
                           ( mn : uint32 )
                           ( ms: address  )
                           ( mv: uint128  )
                           ( tb: uint128  ) 
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := tb $$}            in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_Default := dm $$} in
                       
killBlank_exec_prop eb address_to
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l      $$}
                          with Ledger_VMState := v5       $$}
                          with Ledger_MessagesState := me0 $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck killBlank_exec_propb. *)

Definition killBlank_noexec_prop (eb: uint128) 
                                 (address_to: address)   
                                 (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l in
killBlank_requires eb address_to  l -> 
 Ledger_MainState l = Ledger_MainState l' /\
 Ledger_MessagesState l = Ledger_MessagesState l' /\
 Ledger_VMState l = Ledger_VMState l'.

Definition killBlank_noexec_propb
                           (eb: uint128) 
                           (address_to: address)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                           ( me: MessagesAndEventsLRecord)  : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
killBlank_noexec_prop eb address_to
        {$$
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$}
                          with Ledger_MessagesState := me $$} ? .

(*UNCOMMENT ME*)
(* Time QuickCheck killBlank_noexec_propb.  *)

Definition killBlank_noexec_contract_prop (eb: uint128) 
                                (address_to: address)    
                                (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (killBlank_ (KWMessages_ι_EPSILON_BALANCE_:=eb) address_to)) l in
 Ledger_MainState l = Ledger_MainState l' .

Definition killBlank_noexec_contract_propb
                           (eb: uint128) 
                           (address_to: address)  
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                             : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$}        in
let v2 := {$$ v1 with VMState_ι_now := mn $$}                in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$}         in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$}          in
let v5 := {$$ v4 with VMState_ι_balance := mb $$}            in
                       
killBlank_noexec_contract_prop eb address_to
        {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .


(*UNCOMMENT ME*)
(* Time QuickCheck killBlank_noexec_contract_propb. *)

(* change a little logic on nir < nis, in killBlank and setFundCode *)

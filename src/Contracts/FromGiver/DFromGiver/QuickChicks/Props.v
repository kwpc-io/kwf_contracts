Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.

(* Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
 *)
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
Require Import DFromGiver.Ledger.
Require Import DFromGiver.ClassTypesNotations.
Require Import DFromGiver.ClassTypes.
Require Import DFromGiver.Functions.FuncSig.
Require Import DFromGiver.Functions.FuncNotations.
Require Import DFromGiver.Functions.Funcs.

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

(* Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
 *)
Require Import Project.CommonQCEnvironment.
(* Require Import DFromGiver.QuickChicks.QCEnvironment.
 *)
Definition UinterpreterL := @Uinterpreter XBool XUInteger XMaybe XList XProd XHMap _ _ _ _ _ _
                             LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord
                             MessagesAndEventsLRecord GlobalParamsLRecord
                             OutgoingMessageParamsLRecord ledgerClass .
Arguments UinterpreterL {_} {_} {_}.

Definition ledger_prop1 (l: LedgerLRecord) := true.

(* Set Typeclasses Debug. *)

(* Time QuickChick ledger_prop1.*)

Import FinProof.Common.  (*for eqb!!!*)
Require Import FinProof.CommonInstances.

(* 
Definition implb (a b: bool) := orb (negb a) b.

(* ---------------------------------------------*)
Notation ControlResult := (@ControlResultL) .
Definition isError {R b} (cr : ControlResult R b) : bool :=
 match cr with
 | ControlValue _ _ => false
 | _ => true
 end.
 *)(* ---------------------------------------------*)
(* constructor *)
(* #[global]
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
 *)
Definition MessagesAndEventsDefault : MessagesAndEventsLRecord:= Eval compute in default.
Definition VMStateDefault : VMStateLRecord  := Eval compute in default. 

Definition constructor_requires  (GFM :  uint128)
(lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
                           ( l: LedgerLRecord )  : Prop :=
let fund_address := toValue (eval_state (sRReader || fund_address_  || ) l) in
let intS := toValue (eval_state (sRReader || int_sender () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let require1 := ( intS) <> ( fund_address) in
let require2 := ( fund_address = default ) in
let require3 :=  (uint2N tn >= uint2N lock_time)  in
let require4 :=  (uint2N lock_time >= uint2N unlock_time)  in
 require1 \/ require2  \/ require3 \/ require4.

Definition constructor_isError_prop (GFM :  uint128)
(lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (constructor_   (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) lock_time unlock_time )) l)
<-> constructor_requires GFM lock_time unlock_time l.

 Definition constructor_exec_prop
 (GFM :  uint128)
 (lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
 ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (constructor_   (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) lock_time unlock_time)) l in  
let mm := toValue (eval_state (sRReader IBlankPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || fund_address_ || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in
let giver_address := toValue (eval_state (sRReader || giver_address_ || ) l) in
let params:InternalMessageParamsLRecord := (GFM, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IBlank.IBlank.Interface.IBlank :=
          Interfaces.IBlank.IBlank.Interface.IacknowledgeDeploy giver_address non in
let message := OutgoingInternalMessage params func in 
let ms := isMessageSent message a 0 mm             in  
( ~ (constructor_requires GFM lock_time unlock_time l)  ) ->  
(uint2N (toValue (eval_state (sRReader || balance_ || ) l')) =  0  /\ 
 (toValue (eval_state (sRReader || fund_ready_flag_ || ) l')) =  false /\
uint2N (toValue (eval_state (sRReader || lock_time_ || ) l')) =  uint2N  lock_time /\
uint2N (toValue (eval_state (sRReader || unlock_time_ || ) l')) =  uint2N  unlock_time 
 /\ VMState_ι_accepted (Ledger_VMState l') = true 
 /\ ms = true ).
 
 Definition constructor_noexec_prop 
 (GFM :  uint128)
 (lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
 (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (constructor_  (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) lock_time unlock_time)) l in
constructor_requires GFM lock_time unlock_time l -> 
Ledger_MainState l = Ledger_MainState l'.


(* ---------------------------------- *)
(* receive *)
Definition receive_requires (MB : uint128) ( GFM  : uint128) (  EB : uint128)
                           ( l: LedgerLRecord )  : Prop :=
let mv := toValue (eval_state (sRReader || int_value() || ) l) in
let intS := toValue (eval_state (sRReader || int_sender() || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now() || ) l) in
let lock_time := toValue (eval_state (sRReader || lock_time_ || ) l) in
let giver_address := toValue (eval_state (sRReader || giver_address_ || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in

let if1 := uint2N mv > uint2N MB in
let require1 := intS <> giver_address in
let require2 :=  uint2N tn >= uint2N lock_time in
let require3 :=  uint2N tb <= uint2N mv + uint2N balance + (uint2N GFM + uint2N EB) in
if1 /\ (require1 \/ require2 \/ require3).

Definition receive_isError_prop (MB : uint128) ( GFM  : uint128) (  EB : uint128)
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (receive_ ( KWMessages_ι_FG_MIN_BALANCE_ := MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l)
 <->  (receive_requires MB GFM EB l) .

Definition receive_exec_prop
(MB : uint128) ( GFM  : uint128) (  EB : uint128)
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (receive_  ( KWMessages_ι_FG_MIN_BALANCE_ := MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l in  

let mv := toValue (eval_state (sRReader || int_value() || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let mm := toValue (eval_state (sRReader IBlankPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || fund_address_ || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in
let giver_address := toValue (eval_state (sRReader || giver_address_ || ) l) in
let params:InternalMessageParamsLRecord := (GFM, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IBlank.IBlank.Interface.IBlank :=
          Interfaces.IBlank.IBlank.Interface.InotifyRight giver_address non balance mv in
let message := OutgoingInternalMessage params func in 
let ms := isMessageSent message a 0 mm             in  


( uint2N mv > uint2N MB ) /\ (~ (receive_requires  MB GFM EB l)) ->
VMState_ι_accepted (Ledger_VMState l') = true 
 /\ ms = true
 /\ uint2N (toValue (eval_state (sRReader || balance_ || ) l')) = uint2N balance + uint2N mv. 

Definition receive_noexec_prop
(MB : uint128) ( GFM  : uint128) (  EB : uint128)
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (receive_  ( KWMessages_ι_FG_MIN_BALANCE_ := MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l in 
(receive_requires MB GFM EB l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* notifyParticipant *)
Definition notifyParticipant_requires (  EB : uint128)  (giveup :  boolean  ) (investors_adj_summa_ :  uint128 ) (summa_givers :  uint128 )
                           ( l: LedgerLRecord )  : Prop :=
let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let lock_time := toValue (eval_state (sRReader || lock_time_ || ) l) in
let unlock_time := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let fund_ready_flag := toValue (eval_state (sRReader || fund_ready_flag_ || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let intValue := toValue (eval_state (sRReader || int_value() || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in

let require1 := ms <> fa in
let require2 :=  (((uint2N tn) < (uint2N lock_time)) \/ ((uint2N tn) > (uint2N unlock_time))) in 
let require3 := fund_ready_flag = true in 
let require4 :=  (uint2N tb) < (( uint2N intValue) + (uint2N balance) + (uint2N EB)) in 
require1 \/ require2 \/ require3 \/ require4.

Definition notifyParticipant_isError_prop (  EB : uint128)  (giveup :  boolean  ) (investors_adj_summa_ :  uint128 ) (summa_givers :  uint128 )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (notifyParticipant_ (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup investors_adj_summa_ summa_givers )) l)
 <->  (notifyParticipant_requires EB giveup investors_adj_summa_ summa_givers l) .

Definition notifyParticipant_exec_prop
(  EB : uint128)  (giveup :  boolean  ) (investors_adj_summa_ :  uint128 ) (summa_givers :  uint128 ) 
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyParticipant_  (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup investors_adj_summa_ summa_givers )) l in  
let mm := toValue (eval_state (sRReader IBlankPtr_messages_right ) l') in
let intValue := toValue (eval_state (sRReader || int_value() || ) l) in 
let fund_address := toValue (eval_state (sRReader || fund_address_ || ) l) in 
let giver_address := toValue (eval_state (sRReader || giver_address_ || ) l) in 
let non := toValue (eval_state (sRReader || nonce_ || ) l) in 
let balance := toValue (eval_state (sRReader || balance_ || ) l) in 
let balance' := toValue (eval_state (sRReader || balance_ || ) l') in 
let dead_giver := ( (* giveup  \\ *) (N.eqb (uint2N balance)   0 ) ) in  
let params:InternalMessageParamsLRecord := (intValue, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IBlank.IBlank.Interface.IBlank :=
          Interfaces.IBlank.IBlank.Interface.IacknowledgeFinalizeRight giver_address non dead_giver in
let message := OutgoingInternalMessage params func in  
let ms := isMessageSent message fund_address 0 mm             in  
let mm2 : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in 
let params2 : InternalMessageParamsLRecord := ( balance, (true, Build_XUBInteger 1)) in
let message2 := EmptyMessage PhantomType params2 in 
let ms2 := isMessageSent message2 giver_address 0 mm2 in
let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
let params3:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message3 := EmptyMessage _ params3 in
let ms3 := isMessageSent message3 fund_address 0 mm2 in 
let extra := (* Build_XUBInteger *) ((uint2N balance) * ((uint2N  summa_givers) - (uint2N investors_adj_summa_)) / (uint2N summa_givers) ) in
let params4 : InternalMessageParamsLRecord := ( (Build_XUBInteger extra), (true, Build_XUBInteger 1)) in
let message4 := EmptyMessage PhantomType params4 in 
let ms4 := isMessageSent message4 giver_address 0 mm2 in 


(~ (notifyParticipant_requires  EB giveup investors_adj_summa_ summa_givers l)) ->
VMState_ι_accepted (Ledger_VMState l') = true 
/\ ms = true
/\ ((giveup = true) -> 
               ((uint2N  balance > 0)  -> (ms2 = true)) 
               /\  VMState_ι_isTVMExited (Ledger_VMState l') = true
                                                /\ ms3 = true)
/\ ((giveup  = false ) -> 
               (toValue (eval_state (sRReader || fund_ready_flag_ || ) l') = true) 
               /\ (((uint2N summa_givers) > (uint2N  investors_adj_summa_) )  -> 
                                                                        (* (let extra := (* Build_XUBInteger *) ((uint2N balance) * ((uint2N investors_adj_summa_) - (uint2N summa_givers)) / (uint2N investors_adj_summa_) ) in *)                                                                          
                                                                      (((uint2N balance') = (uint2N balance) - ( extra) )
                                                                      /\ ms4 = true
                                                                      /\ ((  ( uint2N balance) = 0  ) -> ms3 =true)
                                                                      ))).
                                                                   
Definition notifyParticipant_noexec_prop
(  EB : uint128)  (giveup :  boolean  ) (investors_adj_summa_ :  uint128 ) (summa_givers :  uint128 )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyParticipant_  (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup investors_adj_summa_ summa_givers )) l in 
(notifyParticipant_requires EB giveup investors_adj_summa_ summa_givers l) ->
Ledger_MainState l = Ledger_MainState l'.
                   
(* ---------------------------------- *)
(* returnFunds *)
Definition returnFunds_requires (  EB : uint128) 
                           ( l: LedgerLRecord )  : Prop :=
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now() || ) l) in
let unlock_time := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let require1 := ((uint2N tn) <= (uint2N unlock_time))  in
let require2 := (uint2N tb < uint2N EB) in
require1 \/ require2.

Definition returnFunds_isError_prop (  EB : uint128) 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (returnFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB)   )) l)
 <->  (returnFunds_requires  EB   l) .

Definition returnFunds_exec_prop
(  EB : uint128) 
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (returnFunds_   (KWMessages_ι_EPSILON_BALANCE_ := EB)   )) l in  
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let giver_address := toValue (eval_state (sRReader || giver_address_ || ) l) in
let fund_address := toValue (eval_state (sRReader || fund_address_ || ) l) in
let mm : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let params : InternalMessageParamsLRecord := ( balance, (true, Build_XUBInteger 1)) in
let message := EmptyMessage PhantomType params in 
let ms := isMessageSent message giver_address 0 mm in
let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
let params2:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message2 := EmptyMessage _ params2 in
let ms2 := isMessageSent message2 fund_address 0 mm in 
(~ (returnFunds_requires   EB   l)) -> 
VMState_ι_accepted (Ledger_VMState l') = true 
/\ ms2 = true
/\ ((uint2N balance > 0) -> ms = true).

Definition returnFunds_noexec_prop
(  EB : uint128) 
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (returnFunds_   (KWMessages_ι_EPSILON_BALANCE_ := EB)   )) l in 
(returnFunds_requires  EB   l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* acknowledgeFunds *)
Definition acknowledgeFunds_requires 
                           ( l: LedgerLRecord )  : Prop :=
let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let require := ms <> fa in 
require.

Definition acknowledgeFunds_isError_prop 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (acknowledgeFunds_    )) l)
 <->  (acknowledgeFunds_requires    l) .

Definition acknowledgeFunds_exec_prop
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeFunds_     )) l in  
let intS := toValue (eval_state (sRReader || int_sender() || ) l) in
let intV := toValue (eval_state (sRReader || int_value() || ) l) in
let fund_address := toValue (eval_state (sRReader || fund_address_ || ) l) in
let mm : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let params : InternalMessageParamsLRecord := ( intV, (false, Build_XUBInteger 1)) in
let message := EmptyMessage PhantomType params in 
let ms := isMessageSent message intS 0 mm in
let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
let params2:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message2 := EmptyMessage _ params2 in
let ms2 := isMessageSent message2 fund_address 0 mm in 
(~ (acknowledgeFunds_requires    l)) ->
(VMState_ι_accepted (Ledger_VMState l') = true 
/\ ms = true
/\ ms2 = true).

Definition acknowledgeFunds_noexec_prop
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeFunds_     )) l in 
(acknowledgeFunds_requires    l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* sendFunds *)
Definition sendFunds_requires (EB: uint128) (NO_NAME0 :  cell_  )
                           ( l: LedgerLRecord )  : Prop :=

let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let myaddr := toValue (eval_state (sRReader || tvm_myaddr() || ) l) in
let fund_ready_flag := toValue (eval_state (sRReader || fund_ready_flag_ || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in
let intV := toValue (eval_state (sRReader || int_value() || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in

let require1 := ms <> fa in 
(* let require2 := address_to = myaddr in 
 *)let require3 := fund_ready_flag = false in 
let require4 := (uint2N tb) <  (uint2N intV) + (uint2N balance) + (uint2N EB) in 
require1 (* \/ require2 *) \/ require3 \/ require4.
Definition sendFunds_isError_prop (EB: uint128) (NO_NAME0 :  cell_  )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (sendFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) NO_NAME0 )) l)
 <->  (sendFunds_requires  EB NO_NAME0  l) .

Definition sendFunds_exec_prop (EB: uint128) (NO_NAME0 :  cell_  )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (sendFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) NO_NAME0   )) l in  
let intV := toValue (eval_state (sRReader || int_value() || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in
let giver_address := toValue (eval_state (sRReader || giver_address_ || ) l) in

let mm := toValue (eval_state (sRReader IKWFundPtr_messages_right ) l') in
let fund_address := toValue (eval_state (sRReader || fund_address_ || ) l) in
let packParams_eval := toValue (eval_state (Uinterpreter ( packParams_  ) ) l) in
let mvalue := Build_XUBInteger ((uint2N balance) + (uint2N intV)) in
let params:InternalMessageParamsLRecord := (mvalue, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IKWFund.IKWFund.Interface.IKWFund :=
          Interfaces.IKWFund.IKWFund.Interface.IsendFromGiverParams giver_address non packParams_eval in
let message := OutgoingInternalMessage params func in 
let ms := isMessageSent message fund_address 0 mm             in 
(~ (sendFunds_requires  EB  NO_NAME0 l)) ->
(VMState_ι_accepted (Ledger_VMState l') = true 
 /\ ms = true ).

Definition sendFunds_noexec_prop (EB: uint128) (NO_NAME0 :  cell_  )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (sendFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) NO_NAME0   )) l in 
(sendFunds_requires EB  NO_NAME0  l) ->
Ledger_MainState l = Ledger_MainState l'.



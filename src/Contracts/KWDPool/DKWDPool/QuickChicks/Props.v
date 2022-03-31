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

(* Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
 *)
Require Import Project.CommonQCEnvironment.
(* Require Import DKWDPool.QuickChicks.QCEnvironment.
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


Definition constructor_requires (MB :  uint128) (GFM :  uint128)
                           ( final_address: optional address ) 
                           ( l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let lt := toValue (eval_state (sRReader || lock_time_ || ) l) in
let require11 := (uint2N mp = 0) in
let require12 := (uint2N tp <> uint2N mp) in
let require1 := require11 \/ require12 in
let require2 := ( uint2N tb < (uint2N MB) + (uint2N GFM) ) in
let require3 :=   (DKWDPool_ι_fund_address__ (Ledger_MainState l)) = default in
 require1 \/ require2  \/ require3.

 Check constructor_.


 Definition constructor_isError_prop (MB :  uint128) (GFM :  uint128)
                           ( final_address: optional address ) 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (constructor_  (KWMessages_ι_KWD_MIN_BALANCE_:= MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l)
<-> constructor_requires MB GFM final_address l.

 Definition constructor_exec_prop
 ( MB: uint128 )
 ( GFM: uint128 )
 ( final_address: optional address )
 ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (constructor_  (KWMessages_ι_KWD_MIN_BALANCE_:= MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l in  
let mm := toValue (eval_state (sRReader IBlankPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || fund_address_ || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey() || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in
let params:InternalMessageParamsLRecord := (GFM, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IBlank.IBlank.Interface.IBlank :=
          Interfaces.IBlank.IBlank.Interface.IisFundReady tp non in
let message := OutgoingInternalMessage params func in 
let ms := isMessageSent message a 0 mm             in  
( ~ (constructor_requires MB GFM final_address l)  ) ->  
(uint2N (toValue (eval_state (sRReader || balance_ || ) l')) =  0  /\ 
 toValue (eval_state (sRReader || final_address_ || ) l') =  final_address /\
 (toValue (eval_state (sRReader || voting_flag_ || ) l')) =  false /\
 (toValue (eval_state (sRReader || fund_ready_flag_ || ) l')) =  false /\
 (toValue (eval_state (sRReader || initialized_ || ) l')) =  false /\ 
uint2N (toValue (eval_state (sRReader || lock_time_ || ) l')) =  0 /\
uint2N (toValue (eval_state (sRReader || unlock_time_ || ) l')) =  0 /\
uint2N (toValue (eval_state (sRReader || quant_ || ) l')) =  0 /\ 
uint2N (toValue (eval_state (sRReader || farm_rate_ || ) l')) =  0 /\
uint2N (toValue (eval_state (sRReader || kwf_lock_time_ || ) l')) =  0 /\
uint2N (toValue (eval_state (sRReader || init_time_ || ) l')) =  0 /\ 
uint2N (toValue (eval_state (sRReader || deposit_time_ || ) l')) =  0 
 /\ VMState_ι_accepted (Ledger_VMState l') = true 
 /\ ms = true ).
 
 Definition constructor_noexec_prop ( MB: uint128 )
 ( GFM: uint128 )
 ( final_address: optional address )   
 (l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (constructor_ (KWMessages_ι_KWD_MIN_BALANCE_:= MB) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_:= GFM) final_address)) l in
constructor_requires MB GFM final_address l -> 
Ledger_MainState l = Ledger_MainState l'.


 (* ---------------------------------------------*)
(* initialize *)
Definition initialize_requires
(lock_time :  uint32 ) (unlock_time :  uint32 )
                           (quant : ( XUInteger128 ))
                           (rate : ( XUInteger8 ))
                           (kwf_lock_time : ( XUInteger32 )) 
                           ( l: LedgerLRecord )  : Prop :=
let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let init := toValue (eval_state (sRReader || initialized_ || ) l) in
let require1 := ms <> fa in
let require2 := init = true in
let require3 :=  uint2N tn >= uint2N lock_time in
require1 \/ require2 \/ require3.

Definition initialize_isError_prop
(lock_time :  uint32 ) (unlock_time :  uint32 )
                            (quant : ( XUInteger128 ))
                            (rate : ( XUInteger8 ))
                            (kwf_lock_time : ( XUInteger32 )) 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (initialize_  lock_time unlock_time quant rate kwf_lock_time)) l) 
<-> (initialize_requires lock_time unlock_time quant rate kwf_lock_time l).

Definition initialize_exec_prop
                             (lock_time : ( XUInteger32 ))
                             (unlock_time : ( XUInteger32 ))
                             (quant : ( XUInteger128 ))
                             (rate : ( XUInteger8 ))
                             (kwf_lock_time : ( XUInteger32 ))
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (initialize_  lock_time unlock_time quant rate kwf_lock_time )) l in 
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
(~ (initialize_requires lock_time unlock_time quant rate kwf_lock_time l)) ->
(toValue (eval_state (sRReader || quant_ || ) l') = quant /\
toValue (eval_state (sRReader || lock_time_ || ) l') = lock_time /\
toValue (eval_state (sRReader || unlock_time_ || ) l') = unlock_time /\
toValue (eval_state (sRReader || farm_rate_ || ) l') = rate /\ 
toValue (eval_state (sRReader || kwf_lock_time_ || ) l') = kwf_lock_time /\
toValue (eval_state (sRReader || initialized_ || ) l') = true /\
toValue (eval_state (sRReader || init_time_ || ) l') = tn
/\ VMState_ι_accepted (Ledger_VMState l') = true 
).

Definition initialize_noexec_prop
                             (lock_time : ( XUInteger32 ))
                             (unlock_time : ( XUInteger32 ))
                             (quant : ( XUInteger128 ))
                             (rate : ( XUInteger8 ))
                             (kwf_lock_time : ( XUInteger32 ))
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (initialize_  lock_time unlock_time quant rate kwf_lock_time )) l in 
(initialize_requires lock_time unlock_time quant rate kwf_lock_time l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* receive *)
Definition receive_requires (DMF : uint16) ( GFM  : uint128) (  EB : uint128)
                           ( l: LedgerLRecord )  : Prop :=
let mv := toValue (eval_state (sRReader || int_value() || ) l) in
let quant := toValue (eval_state (sRReader || quant_ || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now() || ) l) in
let lock_time := toValue (eval_state (sRReader || lock_time_ || ) l) in
let initialized := toValue (eval_state (sRReader || initialized_ || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in

let require1 := initialized = false in
let if1 := uint2N balance = 0 in
let require2 := uint2N mv < uint2N quant in
let require3 :=  uint2N tb < uint2N mv + (uint2N GFM + uint2N EB) in
let require4 :=  uint2N tn >= uint2N lock_time in
require1 \/ (if1 /\ (require2 \/ require3 \/ require4)).
Definition receive_isError_prop (DMF : uint16) ( GFM  : uint128) (  EB : uint128)
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (receive_ ( KWMessages_ι_DEFAULT_MSG_FLAGS_ := DMF) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l)
 <->  (receive_requires DMF GFM EB l) .

Definition receive_exec_prop
(DMF : uint16) ( GFM  : uint128) (  EB : uint128)
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (receive_  ( KWMessages_ι_DEFAULT_MSG_FLAGS_ := DMF) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l in  
let mm := toValue (eval_state (sRReader IBlankPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || fund_address_ || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey() || ) l) in
let msgsender := toValue (eval_state (sRReader || int_sender() || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in
let quant := toValue (eval_state (sRReader || quant_ || ) l) in 
let f_r := toValue (eval_state (sRReader || farm_rate_ || ) l) in 
let notifyLeft4arg := Build_XUBInteger ( (uint2N quant ) * (uint2N f_r ) / 100  )  in
let params:InternalMessageParamsLRecord := (GFM, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IBlank.IBlank.Interface.IBlank :=
          Interfaces.IBlank.IBlank.Interface.InotifyLeft tp non quant notifyLeft4arg in
let message := OutgoingInternalMessage params func in  
let ms := isMessageSent message a 0 mm             in  
let intVal := toValue (eval_state (sRReader || int_value() || ) l) in
let extra :=  uint2N intVal - uint2N quant in
let mm2 : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let a2 := toValue (eval_state (sRReader || int_sender () || ) l) in
let params2 : InternalMessageParamsLRecord := (Build_XUBInteger extra, (true, DMF)) in
let message2 := EmptyMessage PhantomType params2 in 
let ms2 := isMessageSent message2 a2 0 mm2 in
(~ (receive_requires  DMF GFM EB l)) ->
((uint2N (toValue (eval_state (sRReader || balance_ || ) l)  ) = 0) ->
((toValue (eval_state (sRReader || balance_ || ) l') = quant) /\
(toValue (eval_state (sRReader || deposit_time_ || ) l') = (toValue (eval_state (sRReader || tvm_now () || ) l) ))
 /\ ms = true
 /\ VMState_ι_accepted (Ledger_VMState l') = true )
 /\ ((toValue (eval_state (sRReader || final_address_ || ) l) = None) ->
     (toValue (eval_state (sRReader || final_address_ || ) l') = Some msgsender))
/\  ((extra > (uint2N EB)) -> ms2 = true)).

Definition receive_noexec_prop
(DMF : uint16) ( GFM  : uint128) (  EB : uint128)
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (receive_  ( KWMessages_ι_DEFAULT_MSG_FLAGS_ := DMF) (KWMessages_ι_GAS_FOR_FUND_MESSAGE_ := GFM) (KWMessages_ι_EPSILON_BALANCE_ := EB) )) l in 
(receive_requires DMF GFM EB l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* notifyParticipant *)
Definition notifyParticipant_requires (  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 )
                           ( l: LedgerLRecord )  : Prop :=
let initialized := toValue (eval_state (sRReader || initialized_ || ) l) in
let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now () || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let lock_time := toValue (eval_state (sRReader || lock_time_ || ) l) in
let unlock_time := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let fund_ready_flag := toValue (eval_state (sRReader || fund_ready_flag_ || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let intValue := toValue (eval_state (sRReader || int_value() || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in

let require1 := initialized = false in
let require2 := ms <> fa in 
let require3 :=  (((uint2N tn) < (uint2N lock_time)) \/ ((uint2N tn) > (uint2N unlock_time))) in 
let require4 := fund_ready_flag = true in 
let require5 := (toValue (eval_state (sRReader || final_address_ || ) l) = None) in
let require6 := (uint2N balance) <= 0  in 
let require7 :=  (uint2N tb) < (( uint2N intValue) + (uint2N balance) + (uint2N EB)) in 
require1 \/ require2 \/ require3 \/ require4 \/ require5 \/ require6 \/ require7.

Definition notifyParticipant_isError_prop (  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (notifyParticipant_ (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l)
 <->  (notifyParticipant_requires EB giveup summa_investors summa_givers l) .

Definition notifyParticipant_exec_prop
(  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 ) 
                             ( l: LedgerLRecord )  : Prop :=
let a2 : address := toValue (eval_state (sRReader || final_address_  -> get_default () || ) l) in 
let l' := exec_state (UinterpreterL (notifyParticipant_  (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l in  
let mm := toValue (eval_state (sRReader IBlankPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || fund_address_ || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey() || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in
let intValue := toValue (eval_state (sRReader || int_value() || ) l) in 
let balance := toValue (eval_state (sRReader || balance_ || ) l) in 
let balance' := toValue (eval_state (sRReader || balance_ || ) l') in 
let params:InternalMessageParamsLRecord := (intValue, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IBlank.IBlank.Interface.IBlank :=
          Interfaces.IBlank.IBlank.Interface.IacknowledgeFinalizeLeft tp non  in
let message := OutgoingInternalMessage params func in  
let ms := isMessageSent message a 0 mm             in  
let mm2 : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in 
(* let a2 : address := toValue (eval_state (sRReader || final_address_  -> get_default () || ) l) in true.
 *)let params2 : InternalMessageParamsLRecord := ( balance, (true, Build_XUBInteger 1)) in
let message2 := EmptyMessage PhantomType params2 in 
let ms2 := isMessageSent message2 a2 1 mm2 in
let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
(* let mm3 := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
 *)let params3:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message3 := EmptyMessage _ params3 in
let ms3 := isMessageSent message3 a2 0 mm2 in 
let extra := (* Build_XUBInteger *) ((uint2N balance) * ((uint2N summa_investors) - (uint2N summa_givers)) / (uint2N summa_investors) ) in
(* let mm4 : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let a4 := toValue (eval_state (sRReader || final_address_  || ) l) in
 *)let params4 : InternalMessageParamsLRecord := ( (Build_XUBInteger extra), (true, Build_XUBInteger 1)) in
let message4 := EmptyMessage PhantomType params4 in 
let ifb : bool:= eqb ( uint2N balance)  0 in 
let ms4 := if ( ifb ) then (isMessageSent message4 a2 1 mm2) 
                                        else (isMessageSent message4 a2 0 mm2) in 
(~ (notifyParticipant_requires  EB giveup summa_investors summa_givers l)) ->
VMState_ι_accepted (Ledger_VMState l') = true 
/\ ms = true
/\ ((giveup = true) -> 
               ((uint2N  balance > 0)  -> (ms2 = true)) 
               /\  VMState_ι_isTVMExited (Ledger_VMState l') = true
                                                /\ ms3 = true)
 /\ ((giveup  = false ) -> 
               (toValue (eval_state (sRReader || fund_ready_flag_ || ) l') = true) 
               /\ (((uint2N summa_investors) > (uint2N summa_givers) )  -> 
                                                                        (* (let extra := (* Build_XUBInteger *) ((uint2N balance) * ((uint2N summa_investors) - (uint2N summa_givers)) / (uint2N summa_investors) ) in *)                                                                          
                                                                      (((uint2N balance') = (uint2N balance) - ( extra) )
                                                                      /\ ms4 = true
                                                                      /\ ((  ( uint2N balance) = 0  ) -> ms3 =true)
                                                                      ))).
                                                                   
Definition notifyParticipant_noexec_prop
(  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (notifyParticipant_  (KWMessages_ι_EPSILON_BALANCE_ := EB)  giveup summa_investors summa_givers )) l in 
(notifyParticipant_requires EB giveup summa_investors summa_givers l) ->
Ledger_MainState l = Ledger_MainState l'.
                   
(* ---- setFinalAddress_  -----*)
Definition setFinalAddress_requires (EB :  uint128) 
                           ( final_address:  address ) 
                           ( l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let initialized := toValue (eval_state (sRReader || initialized_ || ) l) in
let require1 := initialized = false in
let require2 := (uint2N mp = 0) in
let require3 := (uint2N tp <> uint2N mp) in
let require4 := ( uint2N tb < (uint2N balance) + (uint2N EB) ) in
 require1 \/ require2  \/ require3 \/ require4.

 Definition setFinalAddress_isError_prop
 (EB :  uint128) 
 ( final_address:  address )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (setFinalAddress_  (KWMessages_ι_EPSILON_BALANCE_ := EB) final_address)) l) 
<-> (setFinalAddress_requires EB final_address l).

Definition setFinalAddress_exec_prop
(EB :  uint128) 
                           ( final_address:  address )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFinalAddress_  (KWMessages_ι_EPSILON_BALANCE_ := EB) final_address )) l in 
(~ (setFinalAddress_requires EB final_address l)) ->
(toValue (eval_state (sRReader || final_address_ || ) l') = Some final_address
/\ VMState_ι_accepted (Ledger_VMState l') = true ).

Definition setFinalAddress_noexec_prop
(EB :  uint128) 
                           ( final_address:  address )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (setFinalAddress_  (KWMessages_ι_EPSILON_BALANCE_ := EB) final_address )) l in 
(setFinalAddress_requires EB final_address l) ->
Ledger_MainState l = Ledger_MainState l'.


(* ---------------------------------- *)
(* returnFunds *)
Definition returnFunds_requires (  EB : uint128) (address_to :  address  )
                           ( l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey () || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey () || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance () || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let initialized := toValue (eval_state (sRReader || initialized_ || ) l) in
let tn := toValue (eval_state (sRReader || tvm_now() || ) l) in
let unlock_time := toValue (eval_state (sRReader || unlock_time_ || ) l) in
let myaddr := toValue (eval_state (sRReader || tvm_myaddr() || ) l) in
let require11 := (uint2N mp = 0) in
let require12 := (uint2N tp <> uint2N mp) in
let require1 := require11 \/ require12 in
let require2 := ( address_to =  myaddr)in
let require3 := ((uint2N tn) <= (uint2N unlock_time)) /\ (initialized = true) in
let require4 := (uint2N tb < uint2N EB) in
require1 \/ require2 \/ require3 \/ require4.

Definition returnFunds_isError_prop (  EB : uint128) (address_to :  address  )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (returnFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) address_to  )) l)
 <->  (returnFunds_requires  EB address_to  l) .

Definition returnFunds_exec_prop
(  EB : uint128) (address_to :  address  )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (returnFunds_   (KWMessages_ι_EPSILON_BALANCE_ := EB) address_to  )) l in  
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let mm2 : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let params2 : InternalMessageParamsLRecord := ( balance, (true, Build_XUBInteger 1)) in
let message2 := EmptyMessage PhantomType params2 in 
let ms2 := isMessageSent message2 address_to 1 mm2 in
let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
(* let mm3 := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
 *)let params3:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message3 := EmptyMessage _ params3 in
let ms3 := isMessageSent message3 address_to 0 mm2 in 
(~ (returnFunds_requires   EB address_to  l)) ->
((toValue (eval_state (sRReader || final_address_ || ) l') = Some address_to)
/\ VMState_ι_accepted (Ledger_VMState l') = true 
/\ ms3 = true
/\ ((uint2N balance > 0) -> ms2 = true)).

Definition returnFunds_noexec_prop
(  EB : uint128) (address_to :  address  )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (returnFunds_   (KWMessages_ι_EPSILON_BALANCE_ := EB) address_to  )) l in 
(returnFunds_requires  EB address_to  l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* acknowledgeFunds *)
Definition acknowledgeFunds_requires 
                           ( l: LedgerLRecord )  : Prop :=
let initialized := toValue (eval_state (sRReader || initialized_ || ) l) in
let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let require1 := initialized = false in
let require2 := ms <> fa in 
require1 \/ require2.

Definition acknowledgeFunds_isError_prop 
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (acknowledgeFunds_    )) l)
 <->  (acknowledgeFunds_requires    l) .

Definition acknowledgeFunds_exec_prop
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeFunds_     )) l in  
let intS := toValue (eval_state (sRReader || int_sender() || ) l) in
let intV := toValue (eval_state (sRReader || int_value() || ) l) in
let mm2 : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let a2 := toValue (eval_state (sRReader || final_address_  -> get_default () || ) l) in
let params2 : InternalMessageParamsLRecord := ( intV, (false, Build_XUBInteger 1)) in
let message2 := EmptyMessage PhantomType params2 in 
let ms2 := isMessageSent message2 intS 0 mm2 in
let flag := N.lor (N.lor (N.lor (uint2N SEND_ALL_GAS) (uint2N SENDER_WANTS_TO_PAY_FEES_SEPARATELY))
                 (uint2N DELETE_ME_IF_I_AM_EMPTY))
						     (uint2N IGNORE_ACTION_ERRORS) in
(* let mm3 := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
 *)let params3:InternalMessageParamsLRecord := (Build_XUBInteger 0, (false, Build_XUBInteger flag)) in
let message3 := EmptyMessage _ params3 in
let ms3 := isMessageSent message3 a2 0 mm2 in 
(~ (acknowledgeFunds_requires    l)) ->
(VMState_ι_accepted (Ledger_VMState l') = true 
/\ ms3 = true
/\ ms2 = true).

Definition acknowledgeFunds_noexec_prop
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (acknowledgeFunds_     )) l in 
(acknowledgeFunds_requires    l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* returnExtraFunds *)
Definition returnExtraFunds_requires (MB : uint128) (EB :uint128 ) (address_to : address )
                           ( l: LedgerLRecord )  : Prop :=
let mp := toValue (eval_state (sRReader || msg_pubkey() || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey() || ) l) in
let require11 := (uint2N mp = 0) in
let require12 := (uint2N tp <> uint2N mp) in
require11 \/ require12.

Definition returnExtraFunds_isError_prop (MB : uint128) (EB :uint128 ) (address_to : address )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (returnExtraFunds_  (KWMessages_ι_KWD_MIN_BALANCE_ := MB) (KWMessages_ι_EPSILON_BALANCE_ := EB) address_to )) l)
 <->  (returnExtraFunds_requires MB EB address_to   l) .

Definition returnExtraFunds_exec_prop
(MB : uint128) (EB :uint128 ) (address_to : address )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (returnExtraFunds_  (KWMessages_ι_KWD_MIN_BALANCE_ := MB) (KWMessages_ι_EPSILON_BALANCE_ := EB) address_to   )) l in  
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let delta := (uint2N tb) - (uint2N balance) - (uint2N MB) in 
let mm : XHMap address (XQueue (OutgoingMessage PhantomType)) := toValue (eval_state (sRReader IDefaultPtr_messages_right ) l') in
let params : InternalMessageParamsLRecord := ( Build_XUBInteger delta, (true, Build_XUBInteger 1)) in
let message := EmptyMessage PhantomType params in 
let ms := isMessageSent message address_to 0 mm in
(~ (returnExtraFunds_requires  MB EB address_to  l)) ->
(VMState_ι_accepted (Ledger_VMState l') = true 
/\ ((delta > (uint2N EB)) ->  ms = true)).

Definition returnExtraFunds_noexec_prop (MB : uint128) (EB :uint128 ) (address_to : address )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (returnExtraFunds_  (KWMessages_ι_KWD_MIN_BALANCE_ := MB) (KWMessages_ι_EPSILON_BALANCE_ := EB) address_to   )) l in 
(returnExtraFunds_requires  MB EB address_to  l) ->
Ledger_MainState l = Ledger_MainState l'.

(* ---------------------------------- *)
(* sendFunds *)
Definition sendFunds_requires (EB: uint128) (code :  cell_  )
                           ( l: LedgerLRecord )  : Prop :=

let initialized := toValue (eval_state (sRReader || initialized_ || ) l) in
let ms := toValue (eval_state (sRReader || int_sender() || ) l) in
let fa := toValue (eval_state (sRReader || fund_address_ || ) l) in
let myaddr := toValue (eval_state (sRReader || tvm_myaddr() || ) l) in
let fund_ready_flag := toValue (eval_state (sRReader || fund_ready_flag_ || ) l) in
let final_address := toValue (eval_state (sRReader || final_address_ || ) l) in
let tb := toValue (eval_state (sRReader || tvm_balance() || ) l) in
let intV := toValue (eval_state (sRReader || int_value() || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in

let require1 := initialized = false in
let require2 := ms <> fa in 
(* let require3 := address_to = myaddr in 
 *)let require4 := fund_ready_flag = false in 
let require5 := final_address = None in 
let require6 := (uint2N tb) <  (uint2N intV) + (uint2N balance) + (uint2N EB) in 
require1 \/ require2 \/ (* require3 \/ *) require4 \/ require5 \/ require6.
Definition sendFunds_isError_prop (EB: uint128) (code :  cell_  )
                           ( l: LedgerLRecord )  : Prop :=
isError (eval_state (UinterpreterL (sendFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) code )) l)
 <->  (sendFunds_requires  EB code  l) .
Check packParams_ _. 
Definition sendFunds_exec_prop (EB: uint128) (code :  cell_  )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (sendFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) code   )) l in  
let intV := toValue (eval_state (sRReader || int_value() || ) l) in
let balance := toValue (eval_state (sRReader || balance_ || ) l) in
let mm := toValue (eval_state (sRReader IKWFundPtr_messages_right ) l') in
let a := toValue (eval_state (sRReader || fund_address_ || ) l) in
let tp := toValue (eval_state (sRReader || tvm_pubkey() || ) l) in
let non := toValue (eval_state (sRReader || nonce_ || ) l) in 
let packParams_eval := toValue (eval_state (Uinterpreter ( packParams_ code   ) ) l) in
let mvalue := Build_XUBInteger ((uint2N balance) + (uint2N intV)) in
let params:InternalMessageParamsLRecord := (mvalue, (true, Build_XUBInteger 1)) in 
let func: Interfaces.IKWFund.IKWFund.Interface.IKWFund :=
          Interfaces.IKWFund.IKWFund.Interface.IsendKWDPoolParams tp non packParams_eval in
let message := OutgoingInternalMessage params func in 
let ms := isMessageSent message a 0 mm             in 
(~ (sendFunds_requires  EB  code l)) ->
(VMState_ι_accepted (Ledger_VMState l') = true 
 /\ ms = true ).

Definition sendFunds_noexec_prop (EB: uint128) (code :  cell_  )
                             ( l: LedgerLRecord )  : Prop :=
let l' := exec_state (UinterpreterL (sendFunds_  (KWMessages_ι_EPSILON_BALANCE_ := EB) code   )) l in 
(sendFunds_requires EB  code  l) ->
Ledger_MainState l = Ledger_MainState l'.



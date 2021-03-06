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

(* 

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
 *)
Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DFromGiver.QuickChicks.QCEnvironment.
Require Import DFromGiver.QuickChicks.Props.

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

(*---------------- *)
(* constructor *)
Definition constructor_isError_propb
                           ( GFM: uint128 )
                           (lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := tb $$} in
                       
constructor_isError_prop  GFM lock_time  unlock_time
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

Definition constructor_exec_propb
                           ( GFM: uint128 )
                           (lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 )  
                           ( bpm : mapping address (queue (OutgoingMessage Interfaces.IBlank.IBlank.Interface.IBlank))) : bool :=

let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := tb $$} in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IBlank := bpm $$} in


constructor_exec_prop  GFM lock_time  unlock_time 
{$$
{$$ 
{$$ LedgerDefault with Ledger_MainState := l      $$}
                  with Ledger_VMState := v5       $$}
                  with Ledger_MessagesState := me0 $$} ? .

Definition constructor_noexec_propb 
( GFM: uint128 )
(lock_time :  XUInteger32 ) (unlock_time :  XUInteger32 ) 
( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$}         in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$}  in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$}   in
let v5 := {$$ v4 with VMState_??_balance := tb $$}     in
                       
constructor_noexec_prop GFM lock_time  unlock_time 
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .

(* ---------------------------------- *)
(* receive *)
Definition receive_isError_propb
(MB : uint128) ( GFM  : uint128) (  EB : uint128)
( l: ContractLRecord )
( pk: uint256 )
( mpk: uint256) 
( mn : uint32 )
( ms: address )
( mv: uint128 )
( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

receive_isError_prop MB GFM EB 
{$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
with Ledger_VMState := v5 $$} ? .

Definition receive_exec_propb
(MB : uint128) ( GFM  : uint128) (  EB : uint128)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  
                           ( bpm : mapping address (queue (OutgoingMessage Interfaces.IBlank.IBlank.Interface.IBlank))) 
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=
                                             
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IBlank := bpm $$} in

receive_exec_prop MB GFM EB 
{$$
{$$ 
{$$ LedgerDefault with Ledger_MainState := l      $$}
                  with Ledger_VMState := v5       $$}
                  with Ledger_MessagesState := me0 $$} ? .

Definition receive_noexec_propb
(MB : uint128) ( GFM  : uint128) (  EB : uint128)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in
                       
receive_noexec_prop MB GFM EB 
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
 
(* ---------------------------------- *)
(* notifyParticipant *)
Definition notifyParticipant_isError_propb
(  EB : uint128)
(giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 )
( l: ContractLRecord )
( pk: uint256 )
( mpk: uint256) 
( mn : uint32 )
( ms: address )
( mv: uint128 )
( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

notifyParticipant_isError_prop EB giveup summa_investors summa_givers
{$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
with Ledger_VMState := v5 $$} ? .

Definition notifyParticipant_exec_propb
(  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                           ( bpm : mapping address (queue (OutgoingMessage Interfaces.IBlank.IBlank.Interface.IBlank))) 
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=

let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IBlank := bpm $$} in
let me2 := {$$ me0 with _OutgoingMessages_Default := dm $$} in 

notifyParticipant_exec_prop EB giveup summa_investors summa_givers 
{$$
{$$ 
{$$ LedgerDefault with Ledger_MainState := l      $$}
                  with Ledger_VMState := v5       $$}
                  with Ledger_MessagesState := me2 $$} ? .

Definition notifyParticipant_noexec_propb
(  EB : uint128)  (giveup :  boolean  ) (summa_investors :  uint128 ) (summa_givers :  uint128 )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in
                       
notifyParticipant_noexec_prop EB giveup summa_investors summa_givers
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .


 
(* ---------------------------------- *)
(* returnFunds *)

 Definition returnFunds_isError_propb
 (  EB : uint128) 
( l: ContractLRecord )
( pk: uint256 )
( mpk: uint256) 
( mn : uint32 )
( ms: address )
( mv: uint128 )
( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

returnFunds_isError_prop  EB   
{$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
with Ledger_VMState := v5 $$} ? .

Definition returnFunds_exec_propb
(  EB : uint128)
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=
                                             
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

let me2 := {$$ MessagesAndEventsDefault with _OutgoingMessages_Default := dm $$} in

returnFunds_exec_prop  EB   
{$$
{$$ 
{$$ LedgerDefault with Ledger_MainState := l      $$}
                  with Ledger_VMState := v5       $$}
                  with Ledger_MessagesState := me2 $$} ? .

Definition returnFunds_noexec_propb
(  EB : uint128) 
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in
                       
returnFunds_noexec_prop  EB   
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .
(* ---------------------------------- *)
(* acknowledgeFunds *)

 Definition acknowledgeFunds_isError_propb
( l: ContractLRecord )
( pk: uint256 )
( mpk: uint256) 
( mn : uint32 )
( ms: address )
( mv: uint128 )
( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

acknowledgeFunds_isError_prop   
{$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
with Ledger_VMState := v5 $$} ? .

Definition acknowledgeFunds_exec_propb
 (final_address :  address  )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  
                           ( dm : mapping address (queue (OutgoingMessage PhantomType))) : bool :=
                                             
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

let me2 := {$$ MessagesAndEventsDefault with _OutgoingMessages_Default := dm $$} in

acknowledgeFunds_exec_prop    
{$$
{$$ 
{$$ LedgerDefault with Ledger_MainState := l      $$}
                  with Ledger_VMState := v5       $$}
                  with Ledger_MessagesState := me2 $$} ? .

Definition acknowledgeFunds_noexec_propb
                  ( l: ContractLRecord )
                  ( pk: uint256 )
                  ( mpk: uint256) 
                  ( mn : uint32 )
                  ( ms: address )
                  ( mv: uint128 )
                  ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in
              
acknowledgeFunds_noexec_prop    
{$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                 with Ledger_VMState := v5 $$} ? .


(* ---------------------------------- *)
(* sendFunds *)
Definition sendFunds_isError_propb (EB: uint128) (NO_NAME0 :  cell_  )
( l: ContractLRecord )
( pk: uint256 )
( mpk: uint256) 
( mn : uint32 )
( ms: address )
( mv: uint128 )
( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in

sendFunds_isError_prop  EB  NO_NAME0
{$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
with Ledger_VMState := v5 $$} ? .

Definition sendFunds_exec_propb
(EB: uint128) (NO_NAME0 :  cell_  )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )
                           ( tb: uint128 )  
                           ( bpm : mapping address (queue (OutgoingMessage Interfaces.IKWFund.IKWFund.Interface.IKWFund))) : bool :=

let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := tb $$} in

let me0 := {$$ MessagesAndEventsDefault with _OutgoingMessages_IKWFund := bpm $$} in

sendFunds_exec_prop  EB   NO_NAME0
{$$
{$$ 
{$$ LedgerDefault with Ledger_MainState := l      $$}
                  with Ledger_VMState := v5       $$}
                  with Ledger_MessagesState := me0 $$} ? .

Definition sendFunds_noexec_propb (EB: uint128) (NO_NAME0 :  cell_  )
                           ( l: ContractLRecord )
                           ( pk: uint256 )
                           ( mpk: uint256) 
                           ( mn : uint32 )
                           ( ms: address )
                           ( mv: uint128 )
                           ( mb: uint128 )  : bool :=
let v0 := {$$ VMStateDefault with VMState_??_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_??_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_??_now := mn $$} in
let v3 := {$$ v2 with VMState_??_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_??_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_??_balance := mb $$} in
                       
sendFunds_noexec_prop  EB  NO_NAME0  
      {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                          with Ledger_VMState := v5 $$} ? .


(* ------------------------------------ *)
(* Start QCTests*)
Extract Constant defNumTests => "10000".
Extract Constant defSize => "7".

(*
Time QuickCheck constructor_isError_propb.
Time QuickCheck constructor_exec_propb.
Time QuickCheck constructor_noexec_propb.
Time QuickCheck receive_isError_propb.
Time QuickCheck receive_exec_propb.
Time QuickCheck receive_noexec_propb.
Time QuickCheck notifyParticipant_isError_propb.
Time QuickCheck notifyParticipant_exec_propb.
Time QuickCheck notifyParticipant_noexec_propb.
Time QuickCheck returnFunds_isError_propb.
Time QuickCheck returnFunds_exec_propb.
Time QuickCheck returnFunds_noexec_propb.
Time QuickCheck acknowledgeFunds_isError_propb.
Time QuickCheck acknowledgeFunds_exec_propb.
Time QuickCheck acknowledgeFunds_noexec_propb.
Time QuickCheck sendFunds_isError_propb.
Time QuickCheck sendFunds_exec_propb.
Time QuickCheck sendFunds_noexec_propb.
 *)
(* 
  
 packParams_
  *) 
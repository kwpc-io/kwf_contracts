Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Project.CommonConstSig.
Require Import Contracts.KWDPool.DKWDPool.ClassTypes.
Require Import Contracts.KWDPool.DKWDPool.Ledger.
Require Import Contracts.KWDPool.DKWDPool.Functions.FuncSig.

Import UrsusNotations.
Local Open Scope ucpp_scope.
Local Open Scope ursus_scope. 



Notation UExpression := (@UExpressionL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass) .
Notation ULValue := (@ULValueL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass) .
Notation URValue := (@URValueL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass) .
Notation wrapULExpression := (@wrapULExpressionL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _ _ _ ).
Notation ursus_call_with_args := (@ursus_call_with_argsL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _  ).
Notation wrapURExpression := (@wrapURExpressionL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _ _ ).
Notation DefaultMessageQueue := (@DefaultMessageQueue LedgerLRecord ContractLRecord LocalStateLRecord MessagesAndEventsLRecord ledgerClass).

(* здесь импортируем все внешние интерфейсы *)

Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.


Definition IKWFundParticipantPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_IKWFundParticipant ) : 
ULValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant )) )) . 
Definition IKWFundParticipantPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IKWFundParticipant ) : 
URValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant ))) false) . 
Notation " 'IKWFundParticipantPtr' " := ( IKWFundParticipantPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition IBlankPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_IBlank ) : 
ULValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IBlank.IBlank.Interface.IBlank )) )) . 
Definition IBlankPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IBlank ) : 
URValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IBlank.IBlank.Interface.IBlank ))) false) . 
Notation " 'IBlankPtr' " := ( IBlankPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition IKWFundPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_IKWFund ) : 
ULValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IKWFund.IKWFund.Interface.IKWFund )) )) . 
Definition IKWFundPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IKWFund ) : 
URValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IKWFund.IKWFund.Interface.IKWFund ))) false) . 
Notation " 'IKWFundPtr' " := ( IKWFundPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.


Definition IDefaultPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_Default ) : 
ULValue ( mapping address (queue (OutgoingMessage PhantomType )) )) . 
Definition IDefaultPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_Default ) : 
URValue ( mapping address (queue (OutgoingMessage PhantomType ))) false) . 
Notation " 'IDefault' " := ( IDefaultPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

#[global] Instance _defaultMessageQueue : DefaultMessageQueue :=
{
    defaultMessageQueue := {{IDefault}}
}.
(* нотации для полей контракта *)

Definition balance__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_balance__ ) : ULValue ( XUInteger128 ) ) . 
Definition balance__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_balance__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'balance_' " := ( balance__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'balance_' " := ( balance__right ) (in custom URValue at level 0) : ursus_scope. 

Definition fund_address__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_fund_address__ ) : ULValue ( address  ) ) . 
Definition fund_address__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_fund_address__ ) : URValue ( address  ) false ) . 
Notation " 'fund_address_' " := ( fund_address__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'fund_address_' " := ( fund_address__right ) (in custom URValue at level 0) : ursus_scope. 

Definition lock_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_lock_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition lock_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_lock_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'lock_time_' " := ( lock_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'lock_time_' " := ( lock_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition unlock_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_unlock_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition unlock_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_unlock_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'unlock_time_' " := ( unlock_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'unlock_time_' " := ( unlock_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition nonce__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_nonce__ ) : ULValue ( XUInteger256 ) ) . 
Definition nonce__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_nonce__ ) : URValue ( XUInteger256 ) false ) . 
Notation " 'nonce_' " := ( nonce__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'nonce_' " := ( nonce__right ) (in custom URValue at level 0) : ursus_scope. 

Definition final_address__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_final_address__ ) : ULValue ( XMaybe  (  address  ) ) ) . 
Definition final_address__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_final_address__ ) : URValue ( XMaybe  (  address  ) ) false ) . 
Notation " 'final_address_' " := ( final_address__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'final_address_' " := ( final_address__right ) (in custom URValue at level 0) : ursus_scope. 

Definition quant__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_quant__ ) : ULValue ( XUInteger128 ) ) . 
Definition quant__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_quant__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'quant_' " := ( quant__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'quant_' " := ( quant__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_flag__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_voting_flag__ ) : ULValue ( XBool  ) ) . 
Definition voting_flag__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_voting_flag__ ) : URValue ( XBool  ) false ) . 
Notation " 'voting_flag_' " := ( voting_flag__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_flag_' " := ( voting_flag__right ) (in custom URValue at level 0) : ursus_scope. 

Definition fund_ready_flag__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_fund_ready_flag__ ) : ULValue ( XBool  ) ) . 
Definition fund_ready_flag__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_fund_ready_flag__ ) : URValue ( XBool  ) false ) . 
Notation " 'fund_ready_flag_' " := ( fund_ready_flag__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'fund_ready_flag_' " := ( fund_ready_flag__right ) (in custom URValue at level 0) : ursus_scope. 

Definition init_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_init_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition init_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_init_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'init_time_' " := ( init_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'init_time_' " := ( init_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition deposit_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_deposit_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition deposit_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_deposit_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'deposit_time_' " := ( deposit_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'deposit_time_' " := ( deposit_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition farm_rate__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_farm_rate__ ) : ULValue ( XUInteger8 ) ) . 
Definition farm_rate__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_farm_rate__ ) : URValue ( XUInteger8 ) false ) . 
Notation " 'farm_rate_' " := ( farm_rate__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'farm_rate_' " := ( farm_rate__right ) (in custom URValue at level 0) : ursus_scope. 

Definition kwf_lock_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_kwf_lock_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition kwf_lock_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_kwf_lock_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'kwf_lock_time_' " := ( kwf_lock_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'kwf_lock_time_' " := ( kwf_lock_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition initialized__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_initialized__ ) : ULValue ( XBool  ) ) . 
Definition initialized__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_initialized__ ) : URValue ( XBool  ) false ) . 
Notation " 'initialized_' " := ( initialized__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'initialized_' " := ( initialized__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_bitmap__left := ( ULState Ledger_MainState (ContractLEmbeddedType DKWDPool_ι_voting_bitmap__ ) : ULValue ( XUInteger256 ) ) . 
Definition voting_bitmap__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DKWDPool_ι_voting_bitmap__ ) : URValue ( XUInteger256 ) false ) . 
Notation " 'voting_bitmap_' " := ( voting_bitmap__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_bitmap_' " := ( voting_bitmap__right ) (in custom URValue at level 0) : ursus_scope. 

Definition serialize {b X} (x: URValue X b):  URValue XUInteger b.
  pose proof (urvalue_bind x (fun _ => || 0 || )).
  rewrite right_or_false in X0.
  refine X0.
Defined.

Definition deserialize {b X}`{XDefault X} (x: URValue XUInteger b) : URValue X b .
  pose proof (urvalue_bind x (fun _ => URScalar default )).
  rewrite right_or_false in X0.
  refine X0.
Defined.

Notation " 'σ' x ":= ( serialize x ) (in custom URValue at level 0 , x custom URValue at level 0).
Notation " 'δ' x ":= ( deserialize x ) (in custom URValue at level 0 , x custom URValue at level 0).
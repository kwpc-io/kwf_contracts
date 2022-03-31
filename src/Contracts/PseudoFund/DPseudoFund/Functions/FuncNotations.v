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
Require Import Contracts.PseudoFund.DPseudoFund.ClassTypes.
Require Import Contracts.PseudoFund.DPseudoFund.Ledger.
Require Import Contracts.PseudoFund.DPseudoFund.Functions.FuncSig.

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

Require Import Contracts.FromGiver.DFromGiver.Interface.
Require Import Contracts.FromGiver.DFromGiver.ClassTypes.

Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.

Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.

Require Import Contracts.KWDPool.DKWDPool.Interface.
Require Import Contracts.KWDPool.DKWDPool.ClassTypes.


Definition IKWFundParticipantPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_IKWFundParticipant ) : 
ULValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant )) )) . 
Definition IKWFundParticipantPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IKWFundParticipant ) : 
URValue ( mapping address (queue (OutgoingMessage Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant ))) false) . 
Notation " 'IKWFundParticipantPtr' " := ( IKWFundParticipantPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition IDFromGiverPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_IDFromGiver ) : 
ULValue ( mapping address (queue (OutgoingMessage Contracts.FromGiver.DFromGiver.Interface.IDFromGiver )) )) . 
Definition IDFromGiverPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IDFromGiver ) : 
URValue ( mapping address (queue (OutgoingMessage Contracts.FromGiver.DFromGiver.Interface.IDFromGiver ))) false) . 
Notation " 'DFromGiverPtr' " := ( IDFromGiverPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

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

Definition IDKWDPoolPtr_messages_left := ( ULState (Ledger_MessagesState) (MessagesAndEventsLEmbeddedType _OutgoingMessages_IDKWDPool ) : 
ULValue ( mapping address (queue (OutgoingMessage Contracts.KWDPool.DKWDPool.Interface.IDKWDPool )) )) . 
Definition IDKWDPoolPtr_messages_right := ( URState (Ledger_MessagesState) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IDKWDPool ) : 
URValue ( mapping address (queue (OutgoingMessage Contracts.KWDPool.DKWDPool.Interface.IDKWDPool ))) false) . 
Notation " 'DKWDPoolPtr' " := ( IDKWDPoolPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.


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

Definition kwdpool_code_hash__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_kwdpool_code_hash__ ) : ULValue ( XUInteger256 ) ) . 
Definition kwdpool_code_hash__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_kwdpool_code_hash__ ) : URValue ( XUInteger256 ) false ) . 
Notation " 'kwdpool_code_hash_' " := ( kwdpool_code_hash__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'kwdpool_code_hash_' " := ( kwdpool_code_hash__right ) (in custom URValue at level 0) : ursus_scope. 

Definition kwdpool_code_depth__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_kwdpool_code_depth__ ) : ULValue ( XUInteger16 ) ) . 
Definition kwdpool_code_depth__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_kwdpool_code_depth__ ) : URValue ( XUInteger16 ) false ) . 
Notation " 'kwdpool_code_depth_' " := ( kwdpool_code_depth__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'kwdpool_code_depth_' " := ( kwdpool_code_depth__right ) (in custom URValue at level 0) : ursus_scope. 

Definition fromgiver_code_hash__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_fromgiver_code_hash__ ) : ULValue ( XUInteger256 ) ) . 
Definition fromgiver_code_hash__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_fromgiver_code_hash__ ) : URValue ( XUInteger256 ) false ) . 
Notation " 'fromgiver_code_hash_' " := ( fromgiver_code_hash__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'fromgiver_code_hash_' " := ( fromgiver_code_hash__right ) (in custom URValue at level 0) : ursus_scope. 

Definition fromgiver_code_depth__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_fromgiver_code_depth__ ) : ULValue ( XUInteger16 ) ) . 
Definition fromgiver_code_depth__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_fromgiver_code_depth__ ) : URValue ( XUInteger16 ) false ) . 
Notation " 'fromgiver_code_depth_' " := ( fromgiver_code_depth__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'fromgiver_code_depth_' " := ( fromgiver_code_depth__right ) (in custom URValue at level 0) : ursus_scope. 

Definition givers_summa__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_givers_summa__ ) : ULValue ( XUInteger128 ) ) . 
Definition givers_summa__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_givers_summa__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'givers_summa_' " := ( givers_summa__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'givers_summa_' " := ( givers_summa__right ) (in custom URValue at level 0) : ursus_scope. 

Definition investors_adj_summa__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_investors_adj_summa__ ) : ULValue ( XUInteger128 ) ) . 
Definition investors_adj_summa__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_investors_adj_summa__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'investors_adj_summa_' " := ( investors_adj_summa__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'investors_adj_summa_' " := ( investors_adj_summa__right ) (in custom URValue at level 0) : ursus_scope. 

Definition investors_summa__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_investors_summa__ ) : ULValue ( XUInteger128 ) ) . 
Definition investors_summa__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_investors_summa__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'investors_summa_' " := ( investors_summa__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'investors_summa_' " := ( investors_summa__right ) (in custom URValue at level 0) : ursus_scope. 

Definition min_summa__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_min_summa__ ) : ULValue ( XUInteger128 ) ) . 
Definition min_summa__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_min_summa__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'min_summa_' " := ( min_summa__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'min_summa_' " := ( min_summa__right ) (in custom URValue at level 0) : ursus_scope. 

Definition max_summa__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_max_summa__ ) : ULValue ( XUInteger128 ) ) . 
Definition max_summa__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_max_summa__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'max_summa_' " := ( max_summa__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'max_summa_' " := ( max_summa__right ) (in custom URValue at level 0) : ursus_scope. 

Definition lock_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_lock_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition lock_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_lock_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'lock_time_' " := ( lock_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'lock_time_' " := ( lock_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition unlock_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_unlock_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition unlock_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_unlock_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'unlock_time_' " := ( unlock_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'unlock_time_' " := ( unlock_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition farm_rate__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_farm_rate__ ) : ULValue ( XUInteger8 ) ) . 
Definition farm_rate__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_farm_rate__ ) : URValue ( XUInteger8 ) false ) . 
Notation " 'farm_rate_' " := ( farm_rate__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'farm_rate_' " := ( farm_rate__right ) (in custom URValue at level 0) : ursus_scope. 

Definition kwf_lock_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_kwf_lock_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition kwf_lock_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_kwf_lock_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'kwf_lock_time_' " := ( kwf_lock_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'kwf_lock_time_' " := ( kwf_lock_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition quant__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_quant__ ) : ULValue ( XUInteger128 ) ) . 
Definition quant__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_quant__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'quant_' " := ( quant__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'quant_' " := ( quant__right ) (in custom URValue at level 0) : ursus_scope. 

Definition nonce__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_nonce__ ) : ULValue ( XUInteger256 ) ) . 
Definition nonce__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_nonce__ ) : URValue ( XUInteger256 ) false ) . 
Notation " 'nonce_' " := ( nonce__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'nonce_' " := ( nonce__right ) (in custom URValue at level 0) : ursus_scope. 

Definition num_investors_sent__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_num_investors_sent__ ) : ULValue ( XUInteger32 ) ) . 
Definition num_investors_sent__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_num_investors_sent__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'num_investors_sent_' " := ( num_investors_sent__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'num_investors_sent_' " := ( num_investors_sent__right ) (in custom URValue at level 0) : ursus_scope. 

Definition num_investors_received__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_num_investors_received__ ) : ULValue ( XUInteger32 ) ) . 
Definition num_investors_received__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_num_investors_received__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'num_investors_received_' " := ( num_investors_received__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'num_investors_received_' " := ( num_investors_received__right ) (in custom URValue at level 0) : ursus_scope. 

Definition can_change_kwdpool_code__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_can_change_kwdpool_code__ ) : ULValue ( XBool  ) ) . 
Definition can_change_kwdpool_code__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_can_change_kwdpool_code__ ) : URValue ( XBool  ) false ) . 
Notation " 'can_change_kwdpool_code_' " := ( can_change_kwdpool_code__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'can_change_kwdpool_code_' " := ( can_change_kwdpool_code__right ) (in custom URValue at level 0) : ursus_scope. 

Definition can_change_fromgiver_code__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_can_change_fromgiver_code__ ) : ULValue ( XBool  ) ) . 
Definition can_change_fromgiver_code__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_can_change_fromgiver_code__ ) : URValue ( XBool  ) false ) . 
Notation " 'can_change_fromgiver_code_' " := ( can_change_fromgiver_code__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'can_change_fromgiver_code_' " := ( can_change_fromgiver_code__right ) (in custom URValue at level 0) : ursus_scope. 

Definition num_from_givers__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_num_from_givers__ ) : ULValue ( XUInteger32 ) ) . 
Definition num_from_givers__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_num_from_givers__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'num_from_givers_' " := ( num_from_givers__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'num_from_givers_' " := ( num_from_givers__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voted_for__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voted_for__ ) : ULValue ( XUInteger128 ) ) . 
Definition voted_for__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voted_for__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'voted_for_' " := ( voted_for__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voted_for_' " := ( voted_for__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voted_against__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voted_against__ ) : ULValue ( XUInteger128 ) ) . 
Definition voted_against__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voted_against__ ) : URValue ( XUInteger128 ) false ) . 
Notation " 'voted_against_' " := ( voted_against__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voted_against_' " := ( voted_against__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_start_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voting_start_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition voting_start_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voting_start_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'voting_start_time_' " := ( voting_start_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_start_time_' " := ( voting_start_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_time__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voting_time__ ) : ULValue ( XUInteger32 ) ) . 
Definition voting_time__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voting_time__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'voting_time_' " := ( voting_time__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_time_' " := ( voting_time__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_result__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voting_result__ ) : ULValue ( XMaybe  (  XBool  ) ) ) . 
Definition voting_result__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voting_result__ ) : URValue ( XMaybe  (  XBool  ) ) false ) . 
Notation " 'voting_result_' " := ( voting_result__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_result_' " := ( voting_result__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_code_hash__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voting_code_hash__ ) : ULValue ( XUInteger256 ) ) . 
Definition voting_code_hash__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voting_code_hash__ ) : URValue ( XUInteger256 ) false ) . 
Notation " 'voting_code_hash_' " := ( voting_code_hash__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_code_hash_' " := ( voting_code_hash__right ) (in custom URValue at level 0) : ursus_scope. 

Definition voting_id__left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_voting_id__ ) : ULValue ( XUInteger32 ) ) . 
Definition voting_id__right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_voting_id__ ) : URValue ( XUInteger32 ) false ) . 
Notation " 'voting_id_' " := ( voting_id__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'voting_id_' " := ( voting_id__right ) (in custom URValue at level 0) : ursus_scope. 

Definition code_updated_left := ( ULState Ledger_MainState (ContractLEmbeddedType DPseudoFund_ι_code_updated_ ) : ULValue ( XBool  ) ) . 
Definition code_updated_right := ( URState Ledger_MainState (H:=ContractLEmbeddedType DPseudoFund_ι_code_updated_ ) : URValue ( XBool  ) false ) . 
Notation " 'code_updated' " := ( code_updated_left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " 'code_updated' " := ( code_updated_right ) (in custom URValue at level 0) : ursus_scope. 
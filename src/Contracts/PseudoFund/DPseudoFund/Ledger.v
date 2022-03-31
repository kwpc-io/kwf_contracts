Require Import Coq.Program.Basics. 
Require Import String. 

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21Instances.  

Require Import UMLang.UrsusLib. 
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmFunc. 
Require Import UrsusTVM.Cpp.tvmTypes. 

Require Import Project.CommonTypes. 
Require Import PseudoFund.DPseudoFund.ClassTypes.
(* блок необходимых интерфейсов *) 

Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import FromGiver.DFromGiver.Interface.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
Require Import KWDPool.DKWDPool.Interface.
Require Import KWDPool.DKWDPool.ClassTypes.
(* **************************** *)
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Set Typeclasses Depth 100.
Inductive MessagesAndEventsFields := 
| _OutgoingMessages_Default
| _OutgoingMessages_IKWFundParticipant
| _OutgoingMessages_IDFromGiver
| _OutgoingMessages_IBlank
| _OutgoingMessages_IKWFund
| _OutgoingMessages_IDKWDPool
| _EmittedEvents
| _GlobalParams
| _OutgoingMessageParams
| _MessagesLog.

Definition ContractFields := DPseudoFundFields.


Definition MessagesAndEventsL : list Type := 
  [( XHMap address (XQueue (OutgoingMessage PhantomType )) ) : Type ;  
( XHMap address (XQueue (OutgoingMessage Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage FromGiver.DFromGiver.Interface.IDFromGiver )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage Interfaces.IBlank.IBlank.Interface.IBlank )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage Interfaces.IKWFund.IKWFund.Interface.IKWFund )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage KWDPool.DKWDPool.Interface.IDKWDPool )) ) : Type ;
( XList TVMEvent ) : Type ;
GlobalParamsLRecord: Type ;
OutgoingMessageParamsLRecord: Type ;
XList XString : Type ] .

GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .  

Definition ContractLRecord := DPseudoFundLRecord . 
Definition ContractLEmbeddedType := DPseudoFundLEmbeddedType.
Inductive LocalFields00I := | ι000 | ι001 .
Definition LocalState00L := [( XHMap (string*nat) ( cell_  )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState00L LocalFields00I . 
Opaque LocalState00LRecord . 
Inductive LocalFields01I := | ι010 | ι011 .
Definition LocalState01L := [( XHMap (string*nat) (slice_ )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState01L LocalFields01I . 
Opaque LocalState01LRecord . 
Inductive LocalFields10I := | ι100 | ι101 .
Definition LocalState10L := [( XHMap (string*nat) ( XUInteger256 )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState10L LocalFields10I . 
Opaque LocalState10LRecord . 
Inductive LocalFields11I := | ι110 | ι111 .
Definition LocalState11L := [( XHMap (string*nat) ( XUInteger16 )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState11L LocalFields11I . 
Opaque LocalState11LRecord . 
(**************** LocalState Tree ***************.
 /\
/\/\
**************** LocalState Tree ***************)

Inductive LocalFields0I := | ι00 | ι01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GeneratePruvendoRecord LocalState0L LocalFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalFields1I := | ι10 | ι11 . 
Definition LocalState1L := [ LocalState10LRecord ; LocalState11LRecord ] . 
GeneratePruvendoRecord LocalState1L LocalFields1I . 
Opaque LocalState1LRecord . 

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
GeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 


Transparent
LocalState00LRecord
LocalState01LRecord
LocalState10LRecord
LocalState11LRecord
LocalState0LRecord
LocalState1LRecord.
Definition LedgerL : list Type := 
 [ ( ContractLRecord ) : Type ; 
 ( ContractLRecord ) : Type ; 
 ( MessagesAndEventsLRecord ) : Type ; 
 ( MessagesAndEventsLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ] .
GeneratePruvendoRecord LedgerL LedgerFields .
(***************************************)
Transparent MessagesAndEventsLRecord .
Transparent ContractLRecord .
Transparent LedgerLRecord .
Transparent LocalStateLRecord.

(***************************************)

#[global]Program Instance ledgerClass : LedgerClass XBool LedgerLRecord ContractLRecord 
                                LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord 
                                GlobalParamsLRecord OutgoingMessageParamsLRecord .
Next Obligation.
refine ( VMStateLEmbeddedType VMState_ι_isCommitted ).
Defined.
Next Obligation.
refine ( MessagesAndEventsLEmbeddedType _GlobalParams ) .
Defined.
Next Obligation.
refine ( MessagesAndEventsLEmbeddedType _OutgoingMessageParams ).
Defined.  
Fail Next Obligation.

#[local]
Obligation Tactic := idtac.

Notation LocalStateField := (LocalStateField XHMap LocalStateLRecord). 

        #[global, program] Instance LocalStateField00 : LocalStateField ( cell_  ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00).
        eapply (LocalState00LEmbeddedType ι001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00).
        eapply (LocalState00LEmbeddedType ι000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField00 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField01 : LocalStateField (slice_ ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01).
        eapply (LocalState01LEmbeddedType ι011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01).
        eapply (LocalState01LEmbeddedType ι010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField01 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField10 : LocalStateField ( XUInteger256 ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10).
        eapply (LocalState10LEmbeddedType ι101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10).
        eapply (LocalState10LEmbeddedType ι100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField10 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField11 : LocalStateField ( XUInteger16 ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11).
        eapply (LocalState11LEmbeddedType ι111). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11).
        eapply (LocalState11LEmbeddedType ι110). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField11 : typeclass_instances. 
        
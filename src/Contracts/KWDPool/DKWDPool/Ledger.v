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
Require Import KWDPool.DKWDPool.ClassTypes.
(* блок необходимых интерфейсов *) 

Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
Require Import Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import Contracts.Interfaces.IKWFund.IKWFund.ClassTypes.
(* **************************** *)
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Set Typeclasses Depth 100.
Inductive MessagesAndEventsFields := 
| _OutgoingMessages_Default
| _OutgoingMessages_IKWFundParticipant
| _OutgoingMessages_IBlank
| _OutgoingMessages_IKWFund
| _EmittedEvents
| _GlobalParams
| _OutgoingMessageParams
| _MessagesLog.

Definition ContractFields := DKWDPoolFields.


Definition MessagesAndEventsL : list Type := 
  [( XHMap address (XQueue (OutgoingMessage PhantomType )) ) : Type ;  
( XHMap address (XQueue (OutgoingMessage Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage Interfaces.IBlank.IBlank.Interface.IBlank )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage Interfaces.IKWFund.IKWFund.Interface.IKWFund )) ) : Type ;
( XList TVMEvent ) : Type ;
GlobalParamsLRecord: Type ;
OutgoingMessageParamsLRecord: Type ;
XList XString : Type ] .

GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .  

Definition ContractLRecord := DKWDPoolLRecord . 
Definition ContractLEmbeddedType := DKWDPoolLEmbeddedType.
Inductive LocalFields0I := | ι00 | ι01 .
Definition LocalState0L := [( XHMap (string*nat) ( XUInteger128 )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState0L LocalFields0I . 
Opaque LocalState0LRecord . 
Inductive LocalFields1I := | ι10 | ι11 .
Definition LocalState1L := [( XHMap (string*nat) (builder_ )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState1L LocalFields1I . 
Opaque LocalState1LRecord . 
(**************** LocalState Tree ***************.
/\
**************** LocalState Tree ***************)

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
GeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 


Transparent
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

        #[global, program] Instance LocalStateField0 : LocalStateField ( XUInteger128 ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0).
        eapply (LocalState0LEmbeddedType ι01). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0).
        eapply (LocalState0LEmbeddedType ι00). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField0 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField1 : LocalStateField (builder_ ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1).
        eapply (LocalState1LEmbeddedType ι11). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1).
        eapply (LocalState1LEmbeddedType ι10). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField1 : typeclass_instances. 
        
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
Require Import Blank.DBlank.ClassTypes.
(* блок необходимых интерфейсов *) 

Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.ClassTypes.
Require Import FromGiver.DFromGiver.Interface.
Require Import FromGiver.DFromGiver.ClassTypes.
Require Import Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import Contracts.Interfaces.IBlank.IBlank.ClassTypes.
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
| _OutgoingMessages_IDKWDPool
| _EmittedEvents
| _GlobalParams
| _OutgoingMessageParams
| _MessagesLog.

Definition ContractFields := DBlankFields.


Definition MessagesAndEventsL : list Type := 
  [( XHMap address (XQueue (OutgoingMessage PhantomType )) ) : Type ;  
( XHMap address (XQueue (OutgoingMessage Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.IKWFundParticipant )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage FromGiver.DFromGiver.Interface.IDFromGiver )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage Interfaces.IBlank.IBlank.Interface.IBlank )) ) : Type ;
( XHMap address (XQueue (OutgoingMessage KWDPool.DKWDPool.Interface.IDKWDPool )) ) : Type ;
( XList TVMEvent ) : Type ;
GlobalParamsLRecord: Type ;
OutgoingMessageParamsLRecord: Type ;
XList XString : Type ] .

GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .  

Definition ContractLRecord := DBlankLRecord . 
Definition ContractLEmbeddedType := DBlankLEmbeddedType.
Inductive LocalFields000I := | ι0000 | ι0001 .
Definition LocalState000L := [( XHMap (string*nat) (builder_ )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState000L LocalFields000I . 
Opaque LocalState000LRecord . 
Inductive LocalFields001I := | ι0010 | ι0011 .
Definition LocalState001L := [( XHMap (string*nat) ( XUInteger128 )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState001L LocalFields001I . 
Opaque LocalState001LRecord . 
Inductive LocalFields010I := | ι0100 | ι0101 .
Definition LocalState010L := [( XHMap (string*nat) ( XBool  )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState010L LocalFields010I . 
Opaque LocalState010LRecord . 
Inductive LocalFields011I := | ι0110 | ι0111 .
Definition LocalState011L := [( XHMap (string*nat) ( address  )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState011L LocalFields011I . 
Opaque LocalState011LRecord . 
Inductive LocalFields100I := | ι1000 | ι1001 .
Definition LocalState100L := [( XHMap (string*nat) ( cell_  )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState100L LocalFields100I . 
Opaque LocalState100LRecord . 
Inductive LocalFields101I := | ι1010 | ι1011 .
Definition LocalState101L := [( XHMap (string*nat) ( XUInteger256 )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState101L LocalFields101I . 
Opaque LocalState101LRecord . 
Inductive LocalFields110I := | ι1100 | ι1101 .
Definition LocalState110L := [( XHMap (string*nat) ( XUInteger16 )) : Type; ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalState110L LocalFields110I . 
Opaque LocalState110LRecord . 
(**************** LocalState Tree ***************.
  /\
 /\/\
/\/\/\\
**************** LocalState Tree ***************)

Inductive LocalFields00I := | ι000 | ι001 . 
Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
GeneratePruvendoRecord LocalState00L LocalFields00I . 
Opaque LocalState00LRecord . 

Inductive LocalFields01I := | ι010 | ι011 . 
Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
GeneratePruvendoRecord LocalState01L LocalFields01I . 
Opaque LocalState01LRecord . 

Inductive LocalFields10I := | ι100 | ι101 . 
Definition LocalState10L := [ LocalState100LRecord ; LocalState101LRecord ] . 
GeneratePruvendoRecord LocalState10L LocalFields10I . 
Opaque LocalState10LRecord . 

Inductive LocalFields0I := | ι00 | ι01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GeneratePruvendoRecord LocalState0L LocalFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalFields1I := | ι10 | ι11 . 
Definition LocalState1L := [ LocalState10LRecord ; LocalState110LRecord ] . 
GeneratePruvendoRecord LocalState1L LocalFields1I . 
Opaque LocalState1LRecord . 

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
GeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 


Transparent
LocalState000LRecord
LocalState001LRecord
LocalState010LRecord
LocalState011LRecord
LocalState100LRecord
LocalState101LRecord
LocalState110LRecord
LocalState00LRecord
LocalState01LRecord
LocalState10LRecord
LocalState1LRecord
LocalState0LRecord.
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

        #[global, program] Instance LocalStateField000 : LocalStateField (builder_ ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000).
        eapply (LocalState000LEmbeddedType ι0001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι000).
        eapply (LocalState000LEmbeddedType ι0000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField000 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField001 : LocalStateField ( XUInteger128 ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001).
        eapply (LocalState001LEmbeddedType ι0011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00). 
eapply TransEmbedded. eapply (_ ι001).
        eapply (LocalState001LEmbeddedType ι0010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField001 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField010 : LocalStateField ( XBool  ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010).
        eapply (LocalState010LEmbeddedType ι0101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι010).
        eapply (LocalState010LEmbeddedType ι0100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField010 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField011 : LocalStateField ( address  ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011).
        eapply (LocalState011LEmbeddedType ι0111). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01). 
eapply TransEmbedded. eapply (_ ι011).
        eapply (LocalState011LEmbeddedType ι0110). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField011 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField100 : LocalStateField ( cell_  ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100).
        eapply (LocalState100LEmbeddedType ι1001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι100).
        eapply (LocalState100LEmbeddedType ι1000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField100 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField101 : LocalStateField ( XUInteger256 ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101).
        eapply (LocalState101LEmbeddedType ι1011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι10). 
eapply TransEmbedded. eapply (_ ι101).
        eapply (LocalState101LEmbeddedType ι1010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField101 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField110 : LocalStateField ( XUInteger16 ).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11). 

        eapply (LocalState110LEmbeddedType ι1101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 
eapply TransEmbedded. eapply (_ ι11). 

        eapply (LocalState110LEmbeddedType ι1100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField110 : typeclass_instances. 
        
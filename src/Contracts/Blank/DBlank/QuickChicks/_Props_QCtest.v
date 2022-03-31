(* Require Import Coq.Program.Basics. 
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
 *)
Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Project.CommonQCEnvironment.
Require Import DBlank.QuickChicks.QCEnvironment.
Require Import DBlank.QuickChicks.Props.
(* Require Import UMLang.ExecGenerator. *)
(* 
Definition UinterpreterL := @Uinterpreter XBool XUInteger XMaybe XList XProd XHMap _ _ _ _ _ _
                             LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord
                             MessagesAndEventsLRecord GlobalParamsLRecord
                             OutgoingMessageParamsLRecord ledgerClass .
Arguments UinterpreterL {_} {_} {_}.

Definition ledger_prop1 (l: LedgerLRecord) := true.

(* Time QuickChick ledger_prop1.*)

Import FinProof.Common.  (*for eqb!!!*)
Require Import FinProof.CommonInstances. *)

(* 
Time QuickCheck constructor_isError_propb.
Time QuickCheck constructor_exec_propb. 
  Time QuickCheck constructor_noexec_propb.  
  Time QuickCheck setFromGiverCode_isError_propb.    
  Time QuickCheck setFromGiverCode_exec_propb.  
  Time QuickCheck setFromGiverCode_noexec_propb.  
  Time QuickCheck setKWDPoolCode_isError_propb.  
  Time QuickCheck setKWDPoolCode_exec_propb.  
  Time QuickCheck setKWDPoolCode_noexec_propb.  
  Time QuickCheck isFundReady_isError_propb.  
  Time QuickCheck isFundReady_exec_propb.  
  Time QuickCheck notifyLeft_isError_propb.  
  Time QuickCheck notifyLeft_exec_propb.  
  Time QuickCheck notifyLeft_noexec_propb.  
  Time QuickCheck deployFromGiver_isError_propb.  
  Time QuickCheck deployFromGiver_exec_propb.  
  Time QuickCheck deployFromGiver_noexec_propb.  
  Time QuickCheck acknowledgeDeploy_isError_propb.  
  Time QuickCheck acknowledgeDeploy_exec_propb.  
  Time QuickCheck acknowledgeDeploy_noexec_propb.   
  Time QuickCheck notifyRight_isError_propb.  
  Time QuickCheck notifyRight_exec_propb.  
  Time QuickCheck notifyRight_noexec_propb.  
  Time QuickCheck acknowledgeFinalizeRight_isError_propb.  
  Time QuickCheck acknowledgeFinalizeRight_exec_propb.  
  Time QuickCheck acknowledgeFinalizeRight_noexec_propb.  
  Time QuickCheck acknowledgeFinalizeLeft_isError_propb.  
  Time QuickCheck acknowledgeFinalizeLeft_exec_propb.  
  Time QuickCheck acknowledgeFinalizeLeft_noexec_propb.  
  Time QuickCheck finalize_isError_propb.  
  Time QuickCheck finalize_exec_propb.  
  Time QuickCheck finalize_noexec_propb.                            
  Time QuickCheck finalize_noexec_contract_propb.  
  Time QuickCheck setFundCode_isError_propb.   
  Time QuickCheck setFundCode_exec_propb.  
  Time QuickCheck setFundCode_noexec_propb.  
  Time QuickCheck setFundCode_contract_noexec_propb.  
  Time QuickCheck killBlank_isError_propb.  
  Time QuickCheck killBlank_exec_propb.  
  Time QuickCheck killBlank_noexec_propb.   
  Time QuickCheck killBlank_noexec_contract_propb.   *)


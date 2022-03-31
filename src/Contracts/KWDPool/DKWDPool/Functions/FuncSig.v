
Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmTypes. 

Require Import Contracts.KWDPool.DKWDPool.ClassTypes.
Require Import Contracts.KWDPool.DKWDPool.Ledger.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

(*Parameter DKWDPool_Ф_isFundReady_ : UExpression ( XBool  ) false .  
Parameter DKWDPool_Ф_getBalance_ : UExpression ( XUInteger128 ) false .  
Parameter DKWDPool_Ф_isInitialized_ : UExpression ( XBool  ) false .  
Parameter modifier_Ф_check_fund_ : UExpression PhantomType false .  
Parameter modifier_Ф_check_init_ : UExpression PhantomType false .  
Parameter DKWDPool_Ф_onVoteAccept_ : UExpression PhantomType true .  
Parameter DKWDPool_Ф_onVoteReject_ : (  XUInteger8  ) -> UExpression PhantomType true .  
Parameter modifier_Ф_check_owner_ : UExpression PhantomType false .  
Parameter DKWDPool_Ф_vote_ : (  XBool   ) -> (  XUInteger8  ) -> (  XUInteger256  ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_returnExtraFunds_ : (  address   ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф__sendFunds_ : (  address   ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_returnFunds_ : (  address   ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_packParams_ : (  cell_   ) -> UExpression ( cell_  ) false .  
Parameter DKWDPool_Ф_sendFunds_ : (  cell_   ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_acknowledgeFunds_ : UExpression PhantomType true .  
Parameter DKWDPool_Ф_setFinalAddress_ : (  address   ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_notifyParticipant_ : (  XBool   ) -> (  XUInteger128  ) -> (  XUInteger128  ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_receive_ : UExpression PhantomType true .  
Parameter DKWDPool_Ф_initialize_ : (  XUInteger32  ) -> (  XUInteger32  ) -> (  XUInteger128  ) -> (  XUInteger8  ) -> (  XUInteger32  ) -> UExpression PhantomType true .  
Parameter DKWDPool_Ф_constructor_ : (  XMaybe  (  address  )  ) -> UExpression PhantomType true .  
*)

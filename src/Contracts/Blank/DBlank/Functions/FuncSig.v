
Require Import FinProof.Common. 

Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmTypes. 

Require Import Contracts.Blank.DBlank.ClassTypes.
Require Import Contracts.Blank.DBlank.Ledger.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

(*Parameter DBlank_Ф_getTimes_ : UExpression ( XUInteger256  #  XUInteger256  #  XUInteger256 ) false .  
Parameter DBlank_Ф_getInvestorsNumbers_ : UExpression ( XUInteger256  #  XUInteger256 ) false .  
Parameter DBlank_Ф_getGiversSum_ : UExpression ( XUInteger128 ) false .  
Parameter DBlank_Ф_getInvestorsSum_ : UExpression ( XUInteger128  #  XUInteger128 ) false .  
Parameter modifier_Ф_check_owner_ : UExpression PhantomType false .  
Parameter DBlank_Ф_killBlank_ : (  address   ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_onCodeUpgrade_ : (  cell_   ) -> UExpression PhantomType false .  
Parameter DBlank_Ф_finalizeVoting_ : UExpression PhantomType false .  
Parameter DBlank_Ф_startVoting_ : (  XUInteger32  ) -> (  XUInteger256  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_tryEarlyComplete_ : UExpression PhantomType false .  
Parameter DBlank_Ф_getKWDPoolAddress_ : (  XUInteger256  ) -> (  XUInteger256  ) -> UExpression ( XUInteger256 ) false .  
Parameter modifier_Ф_check_investor_ : (  XUInteger256  ) -> (  XUInteger256  ) -> UExpression PhantomType false .  
Parameter DBlank_Ф_vote_ : (  XUInteger256  ) -> (  XUInteger256  ) -> (  XBool   ) -> (  XUInteger128  ) -> (  XUInteger8  ) -> (  XUInteger256  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_setFundCode_ : (  cell_   ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_finalize_ : (  XBool   ) -> (  address   ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_buildFromGiverDataInitCell_ : (  address   ) -> (  XUInteger256  ) -> UExpression ( cell_  ) false .  
Parameter DBlank_Ф_getFromGiverAddress_ : (  address   ) -> (  XUInteger256  ) -> UExpression ( XUInteger256 ) false .  
Parameter modifier_Ф_check_giver_ : (  address   ) -> (  XUInteger256  ) -> UExpression PhantomType false .  
Parameter DBlank_Ф_acknowledgeFinalizeRight_ : (  address   ) -> (  XUInteger256  ) -> (  XBool   ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_acknowledgeFinalizeLeft_ : (  XUInteger256  ) -> (  XUInteger256  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_notifyRight_ : (  address   ) -> (  XUInteger256  ) -> (  XUInteger128  ) -> (  XUInteger128  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_acknowledgeDeploy_ : (  address   ) -> (  XUInteger256  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_deployFromGiver_ : (  cell_   ) -> (  address   ) -> (  XUInteger256  ) -> UExpression ( address  ) true .  
Parameter DBlank_Ф_notifyLeft_ : (  XUInteger256  ) -> (  XUInteger256  ) -> (  XUInteger128  ) -> (  XUInteger128  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_isFundReady_ : (  XUInteger256  ) -> (  XUInteger256  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_setKWDPoolCodeHash_ : (  XUInteger256  ) -> (  XUInteger16  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_setFromGiverCodeHash_ : (  XUInteger256  ) -> (  XUInteger16  ) -> UExpression PhantomType true .  
Parameter DBlank_Ф_constructor_ : (  XUInteger128  ) -> (  XUInteger128  ) -> UExpression PhantomType true .  
*)

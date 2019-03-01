Require Import Metalib.Metatheory.
Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.param.
Require Import FcEtt.imports.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(**** Toplevel signature with a fixpoint operator ****)

(*

This module proves the following results:

     Lemma Sig_toplevel: Sig toplevel.


It *should* be the only place in the development that
unfolds the definition of an_toplevel. That way, if we change the
definition of the signature in ett.ott, we only need to change this file.

*)

(* ---------------------------------------------------------- *)

Ltac use_binder f x :=
  pick fresh x and apply f;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- Typing ?ctx ?a ?A ] =>
    assert (Ctx ctx); [econstructor; eauto|idtac]
  end.

Ltac use_binderL f x L :=
  pick fresh x excluding L and apply f;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- Typing ?ctx ?a ?A ] =>
    assert (Ctx ctx); [econstructor; eauto|idtac]
  end.


Lemma E_App_intro :
  forall (G : context) (b : tm)(a B A C : tm),
       Typing G b (a_Pi Rel A B) -> (open_tm_wrt_tm B a) = C ->
       Typing G a A -> Typing G (a_App b (Rho Rel) a) C.
Proof.
  intros. subst.  eapply E_App; eauto.
Qed.

Lemma E_IApp_intro :
  forall (G : context) (b : tm) (a B A C : tm),
       Typing G b (a_Pi Irrel A B) -> (open_tm_wrt_tm B a) = C ->
       Typing G a A -> Typing G (a_App b (Rho Irrel) a_Bullet) C.
Proof.
  intros. subst.  eapply E_IApp; eauto.
Qed.

Lemma FixTy_typing :
  Typing nil FixTy a_Star.
Proof.
  use_binder E_Pi X.
  use_binder E_Pi Z.
  use_binder E_Pi W.
  eauto.
  eauto.
  use_binder E_Pi W.
  eauto. 
Qed.

Definition FixCtx : context := 
  ( FixVar2 , Tm (a_Pi Rel (a_Var_f FixVar1) (a_Var_f FixVar1))) :: ( FixVar1 , Tm a_Star) :: nil.

Definition BodyTy : tm := (a_Var_f FixVar1).

Lemma diff_vars : FixVar1 <> FixVar2.
Proof. 
  unfold FixVar1, FixVar2.
  destruct constants as [s [f [f1 [f2 [j k]]]]].
  split_hyp.
  fsetdec.
Qed.

Lemma CtxFixCtx : Ctx FixCtx.
Proof.
  unfold FixCtx. 
  have h: Ctx [( FixVar1 , Tm a_Star)].
  econstructor; eauto 2.
  econstructor; eauto 2.
  use_binderL E_Pi X {{ FixVar1 }}.
  eauto.
  simpl.
  pose k:= diff_vars. clearbody k. fsetdec.
Qed.

Lemma FixDef_FixTy :
  Typing FixCtx FixDef BodyTy.
Proof.
  unfold FixCtx,FixDef,BodyTy; simpl.
  { eapply E_App_intro; eauto 1.
    + econstructor; eauto using CtxFixCtx.
    + cbn. auto.
    + eapply E_App_intro; simpl; eauto.
      { eapply E_IApp_intro with (a := (a_Var_f FixVar1)); simpl; eauto.
        eapply E_Fam; eauto using CtxFixCtx.
        unfold toplevel, ett_ott.FixTy.
        eauto.
        eapply FixTy_typing; eauto.
        cbn. eauto.
        eapply E_Var; eauto using CtxFixCtx.
      } 
      cbn. auto.
      eapply E_Var; eauto using CtxFixCtx.
  } 
Qed.

Definition FixRolCtx := ( FixVar2 , Nom ) :: nil.


Lemma Fix_roleing : roleing FixRolCtx FixDef Nom.
Proof. 
  unfold FixRolCtx, FixDef.
  econstructor; eauto 2.
  econstructor; eauto 2.
  econstructor; eauto 2.
  econstructor; eauto 2.
  eapply role_a_Fam; eauto 2.
  unfold toplevel; eauto.
  eauto.
  eauto.
Qed. 



Lemma FixPatCtx : PatternContexts FixRolCtx FixCtx [ FixVar1 ] Fix  FixTy FixPat BodyTy.
Proof.
  unfold FixRolCtx, FixCtx, FixPat, FixTy, BodyTy.
  simpl_env.
  have h2:
    PatternContexts [] [] [] Fix FixTy (a_Fam Fix) FixTy.
  { 
    eapply PatCtx_Const.
    unfold FixTy.
    eapply lc_a_Pi; auto.
    intro x. cbn. econstructor; eauto.
    eapply lc_a_Pi; auto.
    intro y. cbn. auto.
    intro y. cbn. auto.
  } 
  set A' := (a_Pi Rel (a_Var_f FixVar1) (a_Var_f FixVar1)).
  set A := (a_Var_f FixVar1).
  set p2:= (a_App (a_Fam Fix) (Rho Irrel) a_Bullet).
  have h: PatternContexts [] [(FixVar1, Tm a_Star)] [FixVar1] Fix FixTy p2 (a_Pi Rel A' A).
  { 
    set AA:= (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1)).
    move: (PatCtx_PiIrr empty [] [] a_Star [] Fix FixTy (a_Fam Fix) AA) => pp2.
    move: (pp2 h2 FixVar1 ltac:(auto)) => pp3.
    unfold p2.
    cbn in pp3.
    unfold A'.
    unfold A.
    eapply pp3.
  } 
  move: (PatCtx_PiRel empty [] Nom [(FixVar1, Tm a_Star)] A' [ FixVar1 ] Fix FixTy) => p1.
  move: (p1 p2 A h FixVar2 ltac:(auto)) => p3.
  cbn in p3.
  fold FixTy.
  eapply p3.
Qed.

Lemma Sig_toplevel: Sig toplevel. Proof. 
  unfold toplevel.
  simpl_env.
  replace [Nom] with (range FixRolCtx).
  eapply Sig_ConsAx; eauto 2.
  eapply FixTy_typing.
  eapply FixPatCtx.
  eapply FixDef_FixTy.
  move=> x In. simpl in *. destruct In. subst. 
  pose k:= diff_vars. move => h. apply k. fsetdec.
  done.
  eapply Fix_roleing.
  cbn. auto.
Qed.

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

     Lemma AnnSig_an_toplevel: AnnSig an_toplevel.
     Lemma Sig_toplevel: Sig toplevel.


It *should* be the only place in the development that
unfolds the definition of an_toplevel. That way, if we change the
definition of the signature in ett.ott, we only need to change this file.

In this case, it uses the fact that an_toplevel (defined in ett.ott)
contains the following definitions:

Definition Fix : atom.
  pick fresh F.
  exact F.
Qed.

Definition FixDef : tm :=
  (a_Abs Irrel a_Star
         (a_Abs Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1))
                (a_App (a_Var_b 0) Rel
                       (a_App (a_App (a_Fam Fix) Irrel (a_Var_b 1)) Rel (a_Var_b 0))))).

Definition FixTy : tm :=
  a_Pi Irrel a_Star
       (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1))
             (a_Var_b 1)).


Lemma AxFix : binds Fix (Ax FixDef FixTy FixTy Nom [Nom]) an_toplevel.
  unfold an_toplevel.
  eauto.
Qed.

Ltac an_use_binder f x :=
  pick fresh x and apply f; eauto;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- AnnTyping ?ctx ?a ?A ?R] =>
    assert (AnnCtx ctx); [econstructor; eauto|idtac]
  end.

Lemma An_App_intro :
  forall (G : context) (b : tm) (rho : relflag) R (a B A C : tm),
       AnnTyping G b (a_Pi rho A B) R -> (open_tm_wrt_tm B a) = C ->
       AnnTyping G a A R -> AnnTyping G (a_App b (Rho rho) a) C R.
Proof.
  intros. subst. eapply An_App; eauto.
Qed.


Lemma FixTy_Star :
  AnnTyping nil FixTy a_Star Nom.
Proof.
  an_use_binder An_Pi X.
  an_use_binder An_Pi Z.
  an_use_binder An_Pi W.
  eauto.
  eauto.
  an_use_binder An_Pi W.
  eauto.
Qed.

Lemma FixDef_FixTy :
  AnnTyping nil FixDef FixTy Nom.
Proof.
  an_use_binder An_Abs X.
  an_use_binder An_Abs x.
  { an_use_binder An_Pi Z. eauto. }
  { an_use_binder An_Pi Z. eauto. }
  { eapply An_App_intro; eauto.
    { eapply An_App_intro; simpl; eauto.
      { eapply An_App_intro; simpl; eauto.
        eapply An_Fam; eauto.
        eapply AxFix.
        an_use_binder An_Pi Z.
        an_use_binder An_Pi W; eauto.
        an_use_binder An_Pi M; eauto.
        an_use_binder An_Pi N; eauto.
        unfold open_tm_wrt_tm. simpl. eauto. }
      unfold open_tm_wrt_tm. simpl. eauto.
    }
  }
Qed.
(*
Lemma AnnSig_an_toplevel: AnnSig an_toplevel.
Proof.
  unfold an_toplevel.
  econstructor; eauto.
(*  eapply AxFix. *)
  eapply FixTy_Star. eauto.
  eapply FixDef_FixTy.
Qed.*)
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

Definition FixPat : tm := 
    a_App (a_App (a_Fam Fix) (Rho Irrel) a_Bullet) (Rho Rel) (a_Var_f FixVar2).

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

(* 
Inductive PatternContexts : role_context -> context -> atom_list -> const -> tm -> tm -> tm -> Prop :=    (* defn PatternContexts *)
 | PatCtx_Const : forall (F:const) (A:tm),
     lc_tm A ->
     PatternContexts  nil   nil   nil  F A (a_Fam F) A
 | PatCtx_PiRel : forall (L:vars) (W:role_context) (R:role) (G:context) (A':tm) (V:atom_list) (F:const) (B p A:tm),
     PatternContexts W G V F B p (a_Pi Rel A' A) ->
      ( forall x , x \notin  L  -> PatternContexts  (( x  ~  R ) ++  W )   (( x ~ Tm  A' ) ++  G )  V F B (a_App p (Role R) (a_Var_f x))  ( open_tm_wrt_tm A (a_Var_f x) )  ) 
 
| PatCtx_PiIrr : forall (L:vars) (W:role_context) (G:context) (A':tm)
    (V:atom_list) (F:const) (B p A:tm),
     PatternContexts W G V F B p (a_Pi Irrel A' A) ->
      ( forall x , x \notin  L  -> 
     PatternContexts W  (( x ~ Tm  A' ) ++  G )  
                  ( x  ::  V )  F B 
     (a_App p (Rho Irrel) a_Bullet)  
     ( open_tm_wrt_tm A (a_Var_f x) )  ) 
 | PatCtx_CPi : forall (L:vars) (W:role_context) (G:context) (phi:constraint) (V:atom_list) (F:const) (B p A:tm),
     PatternContexts W G V F B p (a_CPi phi A) ->
      ( forall c , c \notin  L  -> PatternContexts W  (( c ~ Co  phi ) ++  G )  V F B (a_CApp p g_Triv)  ( open_tm_wrt_co A (g_Var_f c) )  ) .
*)


Lemma FixPatCtx : PatternContexts FixRolCtx FixCtx [ FixVar1 ] Fix  FixTy FixPat BodyTy.
Proof.
  unfold FixRolCtx, FixCtx, FixPat, FixTy, BodyTy.
  simpl_env.
  set A :=  (a_Pi Rel (a_Var_b 0) (a_Var_b 1)).
  replace  (a_Var_f FixVar1) with ( open_tm_wrt_tm A (a_Var_f FixVar2)).
Admitted.

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

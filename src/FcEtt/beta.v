Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Require Import FcEtt.ett_path.

Require Import FcEtt.utils.
Require Export FcEtt.toplevel.
Require Import FcEtt.ett_value.
Require Import FcEtt.ett_match.
Require Import FcEtt.ett_rename.

Lemma Rename_sub p b p1 b1 S1 S2 D' : 
   Rename p b p1 b1 S1 D' ->  S2 [<=] S1 ->
   Rename p b p1 b1 S2 D'.
Proof.
  induction 1; auto.
  econstructor. eapply IHRename. auto. 
  solve_notin.
Qed.



Lemma MatchAgree : forall a p1 b1 b',  MatchSubst a p1 b1 b' -> tm_pattern_agree a p1. 
Proof. 
  intros.
  induction H; auto.
Qed.
    
Lemma MatchSubst_tm_subst a p b b' a1 x : 
  MatchSubst a p b b' ->
  lc_tm a1 ->
  AtomSetImpl.inter (union (singleton x) (fv_tm_tm_tm a1))
                   (union (fv_tm_tm_tm p) (fv_tm_tm_tm b)) [<=] empty ->
  MatchSubst (tm_subst_tm_tm a1 x a) p b (tm_subst_tm_tm a1 x b'). 
Proof.
  intros.
  eapply MatchSubst_subst_tm; auto.
  eapply MatchAgree; eauto.
Qed. 
Lemma MatchSubst_co_subst a p b b' a1 x : 
  MatchSubst a p b b' ->
  lc_co a1 ->
  AtomSetImpl.inter (union (singleton x) (fv_tm_tm_co a1))
    (union (fv_tm_tm_tm p) (fv_co_co_tm b)) [<=] empty ->
  MatchSubst (co_subst_co_tm a1 x a) p b (co_subst_co_tm a1 x b'). 
Proof. 
  intros. 
  eapply MatchSubst_subst_co; auto.
  eapply MatchAgree; eauto.
Qed. 
  
Lemma Beta_tm_subst : forall a a' R b x, Beta a a' R -> lc_tm b -> Beta (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a') R.
Proof.
  intros.
  destruct H.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    apply tm_subst_tm_tm_lc_tm with (a2 := b) (x1:=x) in H; auto.
    eapply Value_tm_subst_tm_tm in H1; eauto.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto 2.
    simpl.
    econstructor.
    apply tm_subst_tm_tm_lc_tm with (a2 := b) (x1:=x) in H; auto.
  - move: (toplevel_inversion H) => [X [G [B [h1 [h2 [h3 h4]]]]]]. 
    eapply Beta_Axiom; eauto.
    admit.
    eapply MatchSubst_tm_subst; eauto.
    admit.
  - simpl. eapply Beta_PatternTrue; eauto with lngen lc. 
    eapply CasePath_subst_tm; eauto with lngen lc.
    eapply ApplyArgs_subst_tm; eauto with lngen lc.
  - simpl. 
    eapply Beta_PatternFalse; eauto with lngen lc.
    apply Value_tm_subst_tm_tm; auto. 
    move => h0. eapply H3.
    eapply CasePath_Value_unsubst_tm; eauto with lngen lc.
Admitted.

Lemma Beta_co_subst : forall a a' R b x, Beta a a' R -> lc_co b -> Beta (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros.
  destruct H.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using co_subst_co_tm_lc_tm.
    apply co_subst_co_tm_lc_tm with (g1 := b) (c1:=x) in H; auto.
    eapply Value_co_subst_co_tm in H1; eauto.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_co; eauto 2.
    simpl.
    econstructor.
    apply co_subst_co_tm_lc_tm with (g1 := b) (c1:=x) in H; auto.
  - move: (toplevel_inversion H) => [X [G [B [h1 [h2 [h3 h4]]]]]]. 
    eapply Beta_Axiom; eauto. 
    admit.
    admit.
  - simpl.
    eapply Beta_PatternTrue; eauto with lngen lc.
    eapply CasePath_subst_co; eauto with lngen lc.
    eapply ApplyArgs_subst_co; eauto with lngen lc.
  - simpl. 
    eapply Beta_PatternFalse; eauto with lngen lc.
    apply Value_co_subst_co_tm; auto. 
    move => h0. eapply H3.
    eapply CasePath_Value_unsubst_co; eauto with lngen lc.
Admitted.

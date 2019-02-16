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
Require Import FcEtt.ett_par.

(* Substitution lemmas for Beta reduction relation *)

Lemma MatchSubst_tm_subst a p b b' a1 x : 
  MatchSubst a p b b' ->
  lc_tm a1 ->
  AtomSetImpl.inter (union (singleton x) (fv_tm_tm_tm a1))
                   (union (fv_tm_tm_tm p) (fv_tm_tm_tm b)) [<=] empty ->
  MatchSubst (tm_subst_tm_tm a1 x a) p b (tm_subst_tm_tm a1 x b'). 
Proof.
  intros.
  eapply MatchSubst_subst_tm; auto.
  eapply MatchSubst_match; eauto.
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
  eapply MatchSubst_match; eauto.
Qed. 
  
Lemma Beta_tm_subst : forall a a' R b x, 
    Beta a a' R -> lc_tm b 
    -> Beta (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a') R.
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
  - move: (toplevel_inversion H) => [X [G [B [h1 [h2 [_ _]]]]]].
    have PP: (Pattern p). eapply axiom_pattern; eauto.
    have LC: lc_tm b0. eapply Typing_lc1; eauto.

    move: (Rename_exists (union (union (fv_tm_tm_tm a) (fv_tm_tm_tm p))
                                (singleton x \u fv_tm_tm_tm b)) PP LC) => 
        [p2 [b2 [D2 h]]].

    eapply Beta_Axiom; eauto.
    eapply Rename_narrow; eauto.
    rewrite fv_tm_tm_tm_tm_subst_tm_tm_upper.
    fsetdec.
    have AG : tm_pattern_agree a p2. eapply tm_pattern_agree_rename_inv_1.
    eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match. eauto.
    eauto. eauto.
    have LC' : lc_tm b2. eapply Rename_lc4. eauto.
    move: (axiom_body_fv_in_pattern H) => h3.

    eapply MatchSubst_tm_subst; eauto.
    replace b' with (matchsubst a p2 b2).
    eapply matchsubst_fun_ind; auto.
 
    
    symmetry.
    eapply MatchSubst_Rename_preserve. eapply tm_pattern_agree_rename_inv_2.
     eapply MatchSubst_match. eauto. eapply H1. eapply H1. eauto.
     fsetdec. fsetdec. eapply uniq_atoms_toplevel. eauto. auto.
     eapply matchsubst_fun_ind; auto.
     
    eapply Rename_inter_sub_empty. eauto. fsetdec.
    eapply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern. eauto. eapply Rename_new_body_fv. 
    eauto. auto.
  - simpl. eapply Beta_PatternTrue; eauto with lngen lc. 
    eapply AppsPath_subst_tm; eauto with lngen lc.
    eapply ApplyArgs_subst_tm; eauto with lngen lc.
  - simpl. 
    eapply Beta_PatternFalse; eauto with lngen lc.
    apply Value_tm_subst_tm_tm; auto. 
    move => h0. eapply H3.
    admit. (* eapply CasePath_Value_unsubst_tm; eauto with lngen lc. *)
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
  - move: (toplevel_inversion H) => [X [G [B [h1 [h2 [_ _]]]]]].
    have PP: (Pattern p). eapply axiom_pattern; eauto.
    have LC: lc_tm b0. eapply Typing_lc1; eauto.

    move: (Rename_exists (union (union (fv_tm_tm_tm a) (fv_tm_tm_tm p))
                                (singleton x \u fv_tm_tm_co b)) PP LC) => 
        [p2 [b2 [D2 h]]].

    eapply Beta_Axiom; eauto.
    eapply Rename_narrow; eauto.
    rewrite fv_tm_tm_tm_co_subst_co_tm_upper.
    fsetdec.
    have AG : tm_pattern_agree a p2. eapply tm_pattern_agree_rename_inv_1.
    eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match. eauto.
    eauto. eauto.
    have LC' : lc_tm b2. eapply Rename_lc4. eauto.
    move: (axiom_body_fv_in_pattern H) => h3.

    eapply MatchSubst_co_subst; eauto.
    replace b' with (matchsubst a p2 b2).
    eapply matchsubst_fun_ind; auto.
 
    
    symmetry.
    eapply MatchSubst_Rename_preserve. eapply tm_pattern_agree_rename_inv_2.
     eapply MatchSubst_match. eauto. eapply H1. eapply H1. eauto.
     fsetdec. fsetdec. eapply uniq_atoms_toplevel. eauto. auto.
     eapply matchsubst_fun_ind; auto.
     
    eapply Rename_inter_sub_empty. eauto. fsetdec.
    eapply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern. eauto. eapply Subset_trans.
    eapply Rename_new_body_fv_co. eauto. eapply axiom_body_fv_co. eauto.
    eapply Subset_empty_any.
  - simpl.
    eapply Beta_PatternTrue; eauto with lngen lc.
    eapply AppsPath_subst_co; eauto with lngen lc.
    eapply ApplyArgs_subst_co; eauto with lngen lc.
  - simpl. 
    eapply Beta_PatternFalse; eauto with lngen lc.
    apply Value_co_subst_co_tm; auto. 
    move => h0. eapply H3.
    admit. (* eapply CasePath_Value_unsubst_co; eauto with lngen lc. *)
Admitted.

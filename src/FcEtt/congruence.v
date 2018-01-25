Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.
Require Import FcEtt.ett_par.

Require Import FcEtt.utils.

Require Import FcEtt.erase_syntax.
Require Import FcEtt.ext_invert.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* ------------------------------------------------------------- *)

Lemma congruence :
  (forall G a A, Typing G a A ->
           forall G1 G2 x A1 a1 a2 D,
             G = G2 ++ [(x, Tm A1)] ++ G1 ->
             Typing G1 a1 A1 ->
             DefEq G1 D a1 a2 A1 ->
             DefEq (map (tm_subst_tm_sort a1 x) G2 ++ G1)
                   D (tm_subst_tm_tm a1 x a) (tm_subst_tm_tm a2 x a)
                    (tm_subst_tm_tm a1 x A)) /\
  (forall G phi,     PropWff G phi       ->
           forall G1 G2 x A1 a1 a2 D,
             G = G2 ++ [(x, Tm A1)] ++ G1 ->
             Typing G1 a1 A1 ->
             DefEq G1 D a1 a2 A1 ->
             Iso (map (tm_subst_tm_sort a1 x) G2 ++ G1)
                    D (tm_subst_tm_constraint a1 x phi) (tm_subst_tm_constraint a2 x phi) ) /\
  (forall G D p1 p2, Iso G D p1 p2      -> True) /\
  (forall G D A B T,   DefEq G D A B T  -> True) /\
  (forall G,           Ctx G            -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; try done.
  - intros G WFG _ G1 G2 x A1 a1 a2 D H0 H1 H2.
    simpl. eapply E_Refl. eapply E_Star.
    destruct (DefEq_regularity H2).
    eapply (fifth tm_substitution_mutual); eauto 2.
  - intros G x A WFG _ B G1 G2 x0 A1 a1 a2 D H1 H2 H3. subst.
    edestruct binds_cases as [ B1 | [B2 | B3]]; split_hyp; eauto 2.
    + replace (tm_subst_tm_tm a2 x0 (a_Var_f x)) with
      (tm_subst_tm_tm a1 x0 (a_Var_f x)).
      eapply (fourth tm_substitution_mutual); eauto 1.
      eapply E_Refl; eauto 1.
      eapply E_Var; eauto 1.
      autorewrite with lngen. reflexivity.
    + inversion H0. subst.
      rewrite tm_subst_tm_tm_var.
      rewrite tm_subst_tm_tm_var.
      eapply DefEq_weakening with (F:=nil)(G := G1); simpl; eauto 2.
      have CTX: Ctx (x0 ~ Tm A1 ++ G1) by eapply Ctx_strengthen; eauto.
      rewrite (tm_subst_fresh_1 _ H2 CTX); auto.
      eapply (fifth tm_substitution_mutual); eauto 1.
    + replace (tm_subst_tm_tm a2 x0 (a_Var_f x)) with
      (tm_subst_tm_tm a1 x0 (a_Var_f x)).
      eapply (fourth tm_substitution_mutual); eauto 1.
      eapply E_Refl; eauto 1.
      eapply E_Var; eauto 1.
      autorewrite with lngen. reflexivity.
  - (* pi *) intros L G rho A B K1 K2 K3 K4 G1 G2 x A1 a1 a2 D H2 H3 H4.
    simpl. subst.
    eapply (@E_PiCong2 (L \u singleton x)); eauto 2.
    + intros x0 Fr. assert (FrL: x0 `notin` L). auto.
    move: (K2 x0 FrL _ ([(x0, Tm A)] ++ G2) x _ _ _ _ eq_refl H3 H4) => h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
    rewrite map_app in h0.
    replace (tm_subst_tm_tm a1 x (a_Var_f x0)) with (a_Var_f x0) in h0.
    replace (tm_subst_tm_tm a2 x (a_Var_f x0)) with (a_Var_f x0) in h0.
    eapply h0.
    rewrite tm_subst_tm_tm_var_neq. auto. auto.
    rewrite tm_subst_tm_tm_var_neq. auto. auto.
    eapply (DefEq_lc H4).
    eapply (DefEq_lc H4).
  - (* abs *)
    intros L G rho a A B H H0 H1 H2 RC G1 G2 x A1 a1 a2 D H3 H4 H5.
    subst. simpl.
    eapply (E_AbsCong (L \u singleton x \u fv_tm_tm_tm a1 \u fv_tm_tm_tm a2)); eauto 2.
    + intros x0 Fr. assert (FrL: x0 `notin` L). auto.
      move: (H0 x0 FrL _ ([(x0, Tm A)] ++ G2) x _ _ _ _ eq_refl H4 H5) => h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
      replace (tm_subst_tm_tm a1 x (a_Var_f x0)) with (a_Var_f x0) in h0.
      replace (tm_subst_tm_tm a2 x (a_Var_f x0)) with (a_Var_f x0) in h0.
      eapply h0.
      rewrite tm_subst_tm_tm_var_neq. auto. auto.
      rewrite tm_subst_tm_tm_var_neq. auto. auto.
      eapply (DefEq_lc H5).
      eapply (DefEq_lc H5).
      eapply (DefEq_lc H5).
    + eapply (first tm_substitution_mutual _ _ _ H1); eauto 2.
    + intros x0 FrLx.
      have h0 := RC x0 ltac:(auto).
      have e1: a_Var_f x0 = tm_subst_tm_tm a1 x (a_Var_f x0); auto.
      * simpl.
        destruct eq_dec; try congruence.
        fsetdec.
      * rewrite e1.
        have lc1: lc_tm a1; try solve [apply Typing_lc in H4; destruct H4; eauto 2].
        rewrite -tm_subst_tm_tm_open_tm_wrt_tm; auto.
        inversion h0; subst.
        -- inversion h0; subst; clear h0.
           apply Rho_Rel; auto.
(*           apply tm_subst_tm_tm_lc_tm; auto. *)
        -- apply Rho_IrrRel; auto.
           inversion h0; subst; clear h0.
           apply tm_subst_tm_tm_fresh; auto.
    + intros x0 FrLx.
      have h0 := RC x0 ltac:(auto).
      have e1: a_Var_f x0 = tm_subst_tm_tm a2 x (a_Var_f x0); auto.
      * simpl.
        destruct eq_dec; try congruence.
        fsetdec.
      * rewrite e1.
        have lc1: lc_tm a2; try solve [apply DefEq_lc in H5 as [h1 [h2 h3]]; destruct H4; eauto 2].
        rewrite -tm_subst_tm_tm_open_tm_wrt_tm; auto.
        inversion h0; subst.
        -- inversion h0; subst; clear h0.
           apply Rho_Rel; auto.
(*           apply tm_subst_tm_tm_lc_tm; auto. *)
        -- apply Rho_IrrRel; auto.
           inversion h0; subst; clear h0.
           apply tm_subst_tm_tm_fresh; auto.
  - (* app rel *) intros G b a B A H K1 K2 K3 G1 G2 x A1 a1 a2 D H1 H2 H3.
    subst. simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm.
    eapply E_AppCong; eauto 2.
    eapply K1; eauto 2.
    eapply (Typing_lc H2).
  - (* app irrel case *)
    intros G b B a A K0 K1 K2 K3 G1 G2 x A1 a1 a2 D H2 H3 H4. subst.
    simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm.
    eapply E_IAppCong.
    eapply K1; eauto.
    fold tm_subst_tm_tm.
    eapply (first tm_substitution_mutual); eauto.
    eapply (DefEq_lc H4).
  - (* conv *)
    intros G a B A t H d H0 t0 H1 G1 G2 x A1 a1 a2 D H2 H3 H4.
    subst.
    move: (@H1 G1 G2 x A1 a1 a2 D eq_refl H3 H4) => h0.
    clear H1.
    move: (@H G1 G2 x A1 a1 a2 D eq_refl H3 H4) => h1.
    clear H.
    eapply E_EqConv. eauto.
    pose K := fourth tm_substitution_mutual _ _ _ _ _ d _ _ _ H3.
    eapply DefEq_weaken_available.
    apply K. auto.
  - (* cpi *)
    intros L G phi B t H p H0 G1 G2 x A1 a1 a2 D H1 H2 H3.
    subst. simpl.
    eapply (@E_CPiCong2 (L \u singleton x)).
    + eapply H0. eauto. eauto. eauto.
    + intros c Fr.
      assert (Frc : c `notin` L). auto.
      move: (@H c Frc G1 ([(c, Co phi)] ++ G2) x A1 a1 a2 D eq_refl H2 H3) => h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_co in h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_co in h0.
      rewrite map_app in h0.
      replace (tm_subst_tm_co a1 x (g_Var_f c)) with (g_Var_f c) in h0.
      replace (tm_subst_tm_co a2 x (g_Var_f c)) with (g_Var_f c) in h0.
      eapply h0.
      simpl. auto.
      simpl. auto.
      eapply (DefEq_lc H3).
      eapply (DefEq_lc H3).
  - (* cabs *)
    intros L G a phi B t H p H0 G1 G2 x A1 a1 a2 D H1 H2 H3.
    subst. simpl.
    eapply (E_CAbsCong (L \u singleton x)).
    + intros c Fr. assert (FrL: c `notin` L). auto.
      move: (@H c FrL _ ([(c, Co phi)] ++ G2) x _ _ _ _ eq_refl H2 H3) => h0.
      repeat (rewrite tm_subst_tm_tm_open_tm_wrt_co in h0).
      rewrite map_app in h0.
      repeat (replace (tm_subst_tm_co a1 x (a_Var_f x0)) with (a_Var_f x0) in h0).
      eapply h0.
      eapply (DefEq_lc H3).
      eapply (DefEq_lc H3).
      eapply (DefEq_lc H3).
    + eapply (second tm_substitution_mutual); eauto 1.
  - (* Capp *)
    intros G a1 B1 a b A t H d H0 G1 G2 x A1 a0 a2 D H1 H2 H3.
    subst. simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_co.
    eapply E_CAppCong with (a:=tm_subst_tm_tm a0 x a)(b:= tm_subst_tm_tm a0 x b); eauto 2.
    eapply (H _ _ x _ _ _ _ eq_refl H2 H3); eauto 2.
    fold tm_subst_tm_tm.
    eapply (fourth tm_substitution_mutual) in d; [idtac|apply H2|eauto].
    eapply DefEq_weaken_available in d.
    eauto.
    eapply (Typing_lc H2).
  - intros. simpl. subst G.
    move: (toplevel_closed b) => h0.
    move: (Typing_regularity h0) => h1.
    have CNil: Ctx [(x, Tm A)]. econstructor; auto.
    rewrite (tm_subst_fresh_2 _ h1 CNil). clear CNil.
    eapply E_Refl.
    eapply E_Fam; eauto 2.
    eapply (fifth tm_substitution_mutual); eauto.
  - intros G a b A t H t0 H0 t1 H1 G1 G2 x A1 a1 a2 D H2 H3 H4.
    simpl.
    pose K1 := H G1 G2 _ _ _ _ _ H2 H3 H4. clearbody K1. clear H.
    pose K2 := H0 _ _ _ _ _ _ _ H2 H3 H4. clearbody K2. clear H0.
    pose K3 := H1 _ _ _ _ _ _ _ H2 H3 H4. clearbody K3. clear H1.
    move: (DefEq_regularity K1) => wf1.
    move: (DefEq_regularity K2) => wf2.
    move: (DefEq_regularity K3) => wf3.
    simpl in K3.
    simpl in wf3.
    inversion wf1.
    inversion wf2.
    inversion wf3.
    subst.
    remember (tm_subst_tm_tm a1 x b) as b1.
    remember (tm_subst_tm_tm a2 x b) as b2.
    remember (tm_subst_tm_tm a1 x a) as a1'.
    remember (tm_subst_tm_tm a2 x a) as a2'.
    remember (tm_subst_tm_tm a1 x A) as A1'.
    remember (tm_subst_tm_tm a2 x A) as A2'.
    remember (map (tm_subst_tm_sort a1 x) G2 ++ G1) as G1'.
    assert (Iso G1' D (Eq a1' b1 A1') (Eq a2' b2 A1')).
    { eapply E_PropCong; eauto. }
    assert (Iso G1' D (Eq a2' b2 A1') (Eq a2' b2 A2')).
    { eapply E_IsoConv; eauto 2.
      eapply E_Wff; eauto 2.
      eapply E_Conv; eauto 2.
      eapply DefEq_weaken_available; eauto.
      eapply E_Conv; eauto 2.
      eapply DefEq_weaken_available; eauto.
    }
    eapply trans_iso. eapply H. auto.
Qed.

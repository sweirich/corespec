Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.
Require Import FcEtt.ett_par.

Require Import FcEtt.utils.
Require Import FcEtt.ext_weak.
Require Import FcEtt.ext_subst.
Require Import FcEtt.ext_invert.
Require Import FcEtt.ett_roleing.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* ------------------------------------------------------------- *)

Lemma congruence :
  (forall G a A, Typing G a A ->
           forall G1 G2 x A1 R a1 a2 D,
             G = G2 ++ [(x, Tm A1)] ++ G1 ->
             Typing G1 a1 A1 ->
             DefEq G1 D a1 a2 A1 Nom ->
             DefEq (map (tm_subst_tm_sort a1 x) G2 ++ G1)
                   D (tm_subst_tm_tm a1 x a) (tm_subst_tm_tm a2 x a)
                    (tm_subst_tm_tm a1 x A) R) /\
  (forall G phi,     PropWff G phi       ->
           forall G1 G2 x A1 a1 a2 D,
             G = G2 ++ [(x, Tm A1)] ++ G1 ->
             Typing G1 a1 A1 ->
             DefEq G1 D a1 a2 A1 Nom ->
             Iso (map (tm_subst_tm_sort a1 x) G2 ++ G1)
                    D (tm_subst_tm_constraint a1 x phi) (tm_subst_tm_constraint a2 x phi) ) /\
  (forall G D p1 p2, Iso G D p1 p2      -> True) /\
  (forall G D A B T R,   DefEq G D A B T R -> True) /\
  (forall G,           Ctx G            -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; try done.
  - intros.
    simpl. eapply E_Refl. eapply E_Star.
    destruct (DefEq_regularity H2).
    eapply (fifth tm_substitution_mutual); eauto 2.
  - intros.
    subst.
    edestruct binds_cases as [ B1 | [B2 | B3]]; split_hyp; eauto 2.
    + replace (tm_subst_tm_tm a2 x0 (a_Var_f x)) with
      (tm_subst_tm_tm a1 x0 (a_Var_f x)).
      eapply (fourth tm_substitution_mutual); eauto 1.
      eapply E_Refl; eauto 1.
      eapply E_Var; eauto 1.
      autorewrite with lngen. reflexivity.
    + inversion H0. inversion H3. subst.
      rewrite tm_subst_tm_tm_var.
      rewrite tm_subst_tm_tm_var.
      eapply DefEq_weakening with (F:=nil)(G := G1); simpl; eauto 2.
      have CTX: Ctx (x0 ~ Tm A1 ++ G1) by eapply Ctx_strengthen; eauto.
      rewrite (tm_subst_fresh_1 _ H1 CTX); auto.
      eapply E_Sub. eauto 1. eauto.
      eapply (fifth tm_substitution_mutual); eauto 1.
    + replace (tm_subst_tm_tm a2 x0 (a_Var_f x)) with
      (tm_subst_tm_tm a1 x0 (a_Var_f x)).
      eapply (fourth tm_substitution_mutual); eauto 1.
      eapply E_Refl; eauto 1.
      eapply E_Var; eauto 1.
      autorewrite with lngen. reflexivity.
  - (* pi *) intros L G rho A B K1 h0 K3 K4 G1 G2 x A1 R0 a1 a2 D H2 H3 H4.
    simpl. subst.
    eapply (@E_PiCong2 (L \u singleton x)); eauto 2.
    intros x0 Fr. assert (FrL: x0 `notin` L). auto.
    clear K4.
    specialize (h0 x0 FrL G1 ([(x0, Tm A)] ++ G2) x A1 R0 a1 a2 D eq_refl H3 H4). 
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0. eauto using Typing_lc1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0. eauto using DefEq_lc2.
    unfold map in h0. unfold EnvImpl.map in h0.
    rewrite map_app in h0.
    replace (tm_subst_tm_tm a1 x (a_Var_f x0)) with (a_Var_f x0) in h0.
    replace (tm_subst_tm_tm a2 x (a_Var_f x0)) with (a_Var_f x0) in h0.
    eapply h0.
    rewrite tm_subst_tm_tm_var_neq. auto. auto.
    rewrite tm_subst_tm_tm_var_neq. auto. auto.

  - (* abs *)
    intros L G rho a A B H H0 H1 H2 RC G1 G2 x A1 R a1 a2 D H3 H4 H5. 
    subst. simpl.
    eapply (E_AbsCong (L \u singleton x \u fv_tm_tm_tm a1 \u fv_tm_tm_tm a2)); eauto 2.
    + intros x0 Fr. assert (FrL: x0 `notin` L). auto.
      move: (H0 x0 FrL _ ([(x0, Tm A)] ++ G2) x A1 R a1 a2 D eq_refl H4 H5) => h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
      eapply DefEq_lc1; eauto.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
      eapply DefEq_lc2; eauto.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0.
      eapply DefEq_lc1; eauto.
      replace (tm_subst_tm_tm a1 x (a_Var_f x0)) with (a_Var_f x0) in h0.
      replace (tm_subst_tm_tm a2 x (a_Var_f x0)) with (a_Var_f x0) in h0.
      eapply h0.
      rewrite tm_subst_tm_tm_var_neq. auto. auto.
      rewrite tm_subst_tm_tm_var_neq. auto. auto.
    + replace a_Star with (tm_subst_tm_tm a1 x a_Star).
      eapply (first tm_substitution_mutual); eauto 2. 
      simpl. auto.
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
  - (* app rel *) intros. 
    subst. simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2 using Typing_lc1.
    eapply E_AppCong; eauto 2.
    eapply H; eauto 2.
  - (* TApp case *)
    intros. subst. simpl.
    have IHb: DefEq (map (tm_subst_tm_sort a1 x) G2 ++ G1) D
                (tm_subst_tm_tm a1 x b)
                (tm_subst_tm_tm a2 x b)
                (tm_subst_tm_tm a1 x (a_Pi Rel A B)) R0.
    { eauto. } clear H.
    have IHa: DefEq (map (tm_subst_tm_sort a1 x) G2 ++ G1) D
                (tm_subst_tm_tm a1 x a)
                (tm_subst_tm_tm a2 x a)
                (tm_subst_tm_tm a1 x A) (param R R0).
    { eauto. } 
    
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2 using Typing_lc1.    
    eapply E_TAppCong; eauto 2.
    eapply RolePath_subst; eauto 2 using Typing_lc1.
    eapply RolePath_subst; eauto 2 using DefEq_lc2.
    simpl in IHb.
    have Tb: Typing (map (tm_subst_tm_sort a1 x) G2 ++ G1) 
                 (tm_subst_tm_tm a2 x b)
                 (a_Pi Rel (tm_subst_tm_tm a1 x A) (tm_subst_tm_tm a1 x B)).
    { autoreg. auto. }
    have Ta: Typing (map (tm_subst_tm_sort a1 x) G2 ++ G1) 
                 (tm_subst_tm_tm a2 x a)
                 (tm_subst_tm_tm a1 x A).
    { autoreg. auto. }
    eapply E_Conv with 
        (A := (open_tm_wrt_tm (tm_subst_tm_tm a1 x B) (tm_subst_tm_tm a2 x a))).
    eapply E_TApp; eauto 2.
    eapply RolePath_subst; eauto 2 using DefEq_lc2.
    eapply E_Sym.
    eapply E_PiSnd with (A1 := tm_subst_tm_tm a1 x A) 
                        (A2 := tm_subst_tm_tm a1 x A) (rho:=Rel); eauto 1.
    admit. (* OK, substitution *)
    eapply H0; eauto 2. eapply (fourth weaken_available_mutual).
    eapply DefEq_weaken_available; eauto 1.
    rewrite dom_app. fsetdec.
    replace a_Star with (tm_subst_tm_tm a1 x a_Star).
    admit. (* Ok, substitution *)
    simpl. auto.
  - (* app irrel case *)
    intros. subst.
    simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2 using Typing_lc1.
    eapply E_IAppCong.
    eapply H; eauto 3.
    fold tm_subst_tm_tm.
    eapply (first tm_substitution_mutual); eauto.
  - (* conv *)
    intros.
    subst.
    move: (@H1 G1 G2 x A1 R a1 a2 D eq_refl H3 H4) => h0.
    clear H1.
    move: (@H G1 G2 x A1 R a1 a2 D eq_refl H3 H4) => h1.
    clear H.
    eapply E_EqConv. eauto.
    pose K := fourth tm_substitution_mutual _ _ _ _ _ _ d _ _ _ H3.
    eapply DefEq_weaken_available.
    apply K. auto.
    move: (DefEq_regularity h0) => h2. inversion h2. subst.
    auto. 
  - (* cpi *)
    intros L G phi B t H p H0 G1 G2 x A1 R a1 a2 D H1 H2 H3.
    destruct phi; subst. simpl.
    eapply (@E_CPiCong2 (L \u singleton x)).
    + eapply H0. eauto. eauto. eauto.
    + intros c Fr.
      assert (Frc : c `notin` L). auto.
      move: (@H c Frc G1 ([(c, Co (Eq a b A R0))] ++ G2) x A1 R a1 a2 D eq_refl H2 H3) => h0.
      rewrite tm_subst_tm_tm_open_tm_wrt_co in h0; eauto 2 using Typing_lc1.
      rewrite tm_subst_tm_tm_open_tm_wrt_co in h0; eauto 2 using DefEq_lc2.
  - (* cabs *)
    intros L G a phi B t H p H0 G1 G2 x A1 R' a1 a2 D H1 H2 H3.
    subst. simpl.
    eapply (E_CAbsCong (L \u singleton x)).
    + intros c Fr. assert (FrL: c `notin` L). auto.
      move: (@H c FrL G1 ([(c, Co phi)] ++ G2) x A1 R' a1 a2 D eq_refl H2 H3) => h0.
      repeat (rewrite tm_subst_tm_tm_open_tm_wrt_co in h0).
      eapply Typing_lc1; eauto.
      eapply DefEq_lc2; eauto.
      eapply Typing_lc1; eauto.
      unfold map in h0.
      rewrite EnvImpl.map_app in h0.
      repeat (replace (tm_subst_tm_co a1 x (a_Var_f x0)) with (a_Var_f x0) in h0).
      eapply h0.
    + eapply (second tm_substitution_mutual); eauto 1.
  - (* Capp *)
    intros G a1 B1 a b A R' t H d H0 G1 G2 x A1 R0 a0 a2 D H1 H2 H3.
    subst. simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto 2 using Typing_lc1.
    eapply E_CAppCong with (a:=tm_subst_tm_tm a0 x a)(b:= tm_subst_tm_tm a0 x b); eauto 2.
    eapply (H _ _ x _ _ _ _ _ eq_refl H2 H3); eauto 2.
    fold tm_subst_tm_tm.
    eapply (fourth tm_substitution_mutual) in d; [idtac|apply H2|eauto].
    eapply DefEq_weaken_available in d.
    eauto.
    simpl_env. auto.
  - intros. simpl. subst G.
    eapply E_Refl.
    eapply E_Const.
    eapply (fifth tm_substitution_mutual); eauto 2.
    erewrite tm_subst_fresh_2; auto; eauto 2.
    erewrite tm_subst_fresh_2; eauto 2.
  - intros. simpl. subst G.
    move: (toplevel_inversion b) => [W0 [G0 [D0 [B0 h0]]]].
    split_hyp.
    admit. 
(*    move: (Typing_regularity h0) => h1.
    have CNil: Ctx [(x, Tm A R)]. econstructor; auto. eauto.
    rewrite (tm_subst_fresh_2 _ h1 CNil). clear CNil.
    eapply E_Refl.
    eapply E_Fam; eauto 2.
    eapply (fifth tm_substitution_mutual); eauto. *)
  - intros. simpl. eapply E_PatCong; eauto 2.
    (* BranchTyping_tm_subst. *)
    admit.
    admit.
    admit.
    admit.
  - intros G a b A R t H t0 H0 t1 H1 G1 G2 x A1 a1 a2 D H2 H3 H4.
    simpl.
    pose K1 := H G1 G2 _ _ R _ _ _ H2 H3 H4. clearbody K1. clear H.
    pose K2 := H0 _ _ _ _ R _ _ _ H2 H3 H4. clearbody K2. clear H0.
    pose K3 := H1 _ _ _ _ R _ _ _ H2 H3 H4. clearbody K3. clear H1.
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
    assert (Iso G1' D (Eq a1' b1 A1' R) (Eq a2' b2 A1' R)).
    { eapply E_PropCong; eauto. }
    assert (Iso G1' D (Eq a2' b2 A1' R) (Eq a2' b2 A2' R)).
    { eapply E_IsoConv; eauto 2.
      eapply E_Wff; eauto 2.
      eapply E_Conv; eauto 2.
      eapply E_Sub; eauto 2.
      eapply E_Conv; eauto 2.
      eapply E_Sub; eauto 2.
    }
    eapply trans_iso. eapply H. auto. Unshelve. all: eauto.
Admitted.

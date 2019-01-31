Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Require Import FcEtt.ett_roleing.
Require Import FcEtt.ett_match.
Require Import FcEtt.ett_path.
Require Import FcEtt.ett_rename.

Import ext_wf.


(* Require Import FcEtt.erase_syntax. *)

Require Export FcEtt.toplevel.

Require Export FcEtt.ett_value.


Lemma roleing_match : forall W1 a R1 W2 p b R2 b', roleing W1 a R1 ->
      roleing (W2 ++ rev (combine (vars_Pattern p) (pat_app_roles p))) b R2 ->
      MatchSubst a p b b' ->
      uniq (W2 ++ rev (combine (vars_Pattern p) (pat_app_roles p)) ++ W1) ->
      roleing (W2 ++ W1) b' R2.
Proof. intros. generalize dependent W1. generalize dependent W2.
       induction H1; intros.
        - simpl in H0.
          replace (W2 ++ W1) with (W2 ++ W1 ++ nil).
          apply roleing_app_rctx. simpl_env. auto. auto. rewrite app_nil_r. auto.
        - simpl in *.
          inversion H2; subst. eapply subst_tm_roleing. rewrite app_assoc.
          eapply IHMatchSubst.
          rewrite combine_app in H0. rewrite rev_app_distr in H0.
          simpl in H0. rewrite <- app_assoc. eauto.
          auto.
          rewrite combine_app in H3. rewrite rev_app_distr in H3.
          simpl in H3. rewrite <- app_assoc. auto. auto.
        - simpl in H0. inversion H2; subst. eauto.
        - simpl in H0. inversion H; subst. eauto.
Qed.


Lemma roleing_apply : forall W a R0 b c R, roleing W a R0 -> roleing W b R ->
                      ApplyArgs a b c -> roleing W c R.
Proof. intros. induction H1; intros; auto.
        - inversion H; subst; eauto.
        - inversion H; subst. econstructor; eauto.
Qed.


Lemma Par_roleing_tm_fst : forall W a a' R, Par W a a' R -> 
                                               roleing W a R.
Proof. intros W a a' R H. induction H; eauto. 
       all: try solve [destruct nu; eauto].
Qed.

Lemma Par_roleing_tm_snd : forall W a a' R, Par W a a' R -> roleing W a' R.
Proof. intros W a a' R H. induction H; eauto.
        - inversion IHPar1; subst. pick fresh x.
          erewrite tm_subst_tm_tm_intro; eauto.
          replace W with (nil ++ W); auto. eapply subst_tm_roleing; eauto.
        - destruct nu; eauto.
        - inversion IHPar; subst. pick fresh c.
          erewrite co_subst_co_tm_intro; eauto.
          replace W with (nil ++ W); auto. eapply subst_co_roleing; eauto.
        - apply toplevel_inversion in H.
          inversion H as [W1 [G1 [B1 [P1 [P2 [P3 P4]]]]]]. inversion P1; subst.
          replace W with (nil ++ W ++ nil); auto.
          apply roleing_app_rctx; simpl_env. auto.
          eapply roleing_sub; eauto. simpl. apply app_nil_r.
        - apply toplevel_inversion in H.
          inversion H as [W1 [G [B [h1 [_ [h2 _]]]]]].
          apply pat_ctx_rctx in h1. subst.
          replace W with (nil ++ W); eauto.
          destruct nu.
          + eapply roleing_match.
            eapply role_a_TApp. eapply IHPar1. eapply IHPar2.
            eapply roleing_Rename. eauto.
            simpl. eapply Rename_inter_sub_empty. eauto.
            rewrite union_empty_r. eauto. eapply Rename_fv_new_pattern. eauto.
            simpl_env. eapply roleing_sub; eauto. auto. simpl_env.
            apply uniq_app. apply uniq_rev. eapply uniq_new_pattern_ctx. eauto.
            eapply rctx_uniq; eauto. unfold disjoint.
            rewrite AtomSetProperties.inter_sym. eapply Rename_inter_sub_empty.
            eauto. eauto. intro. intro. eapply new_pattern_fv. eauto.
            apply dom_rev in H6. rewrite rev_involutive in H6. auto.
          + destruct rho. inversion H4. eapply roleing_match.
            eapply role_a_App. eapply IHPar1. eapply IHPar2.
            eapply roleing_Rename. eauto.
            simpl. eapply Rename_inter_sub_empty. eauto.
            rewrite union_empty_r. eauto. eapply Rename_fv_new_pattern. eauto.
            simpl_env. eapply roleing_sub; eauto. eauto. simpl_env.
            apply uniq_app. apply uniq_rev. eapply uniq_new_pattern_ctx. eauto.
            eapply rctx_uniq; eauto. unfold disjoint.
            rewrite AtomSetProperties.inter_sym. eapply Rename_inter_sub_empty.
            eauto. eauto. intro. intro. eapply new_pattern_fv. eauto.
            apply dom_rev in H6. rewrite rev_involutive in H6. auto.
        - apply toplevel_inversion in H.
          inversion H as [W1 [G [B [h1 [_ [h2 _]]]]]].
          apply pat_ctx_rctx in h1. subst.
          replace W with (nil ++ W); eauto.
          eapply roleing_match.
          eapply role_a_CApp. eapply IHPar.
          eapply roleing_Rename. eauto.
          simpl. eapply Rename_inter_sub_empty. eauto.
          rewrite union_empty_r. eauto. eapply Rename_fv_new_pattern. eauto.
          simpl_env. eapply roleing_sub; eauto. auto. simpl_env.
          apply uniq_app. apply uniq_rev. eapply uniq_new_pattern_ctx. eauto.
          eapply rctx_uniq; eauto. unfold disjoint.
          rewrite AtomSetProperties.inter_sym. eapply Rename_inter_sub_empty.
          eauto. eauto. intro. intro. eapply new_pattern_fv. eauto.
          apply dom_rev in H5. rewrite rev_involutive in H5. auto.
        - econstructor. eapply roleing_apply. eapply IHPar1.
          eapply IHPar2. eauto.
Qed.

Lemma Rename_exists: forall p b D, Pattern p -> lc_tm b ->
             exists p' b' D', Rename p b p' b' D D'.
Proof. intros. exists (rename p b D).1.1, (rename p b D).1.2, (rename p b D).2.
       eapply rename_Rename; eauto.
Qed.

Lemma par_app_rctx : forall W1 W2 W3 a a' R, uniq (W1 ++ W2 ++ W3) ->
                     Par (W1 ++ W3) a a' R ->
                     Par (W1 ++ W2 ++ W3) a a' R.
Proof. intros W1 W2 W3 a a' R U H. generalize dependent W2.
       dependent induction H; intros; eauto.
       all: try solve [econstructor; eauto 3 using roleing_app_rctx].
        - eapply Par_Abs with (L := union L (dom (W1 ++ W2 ++ W3))).
          intros. rewrite app_assoc.
          eapply H0; eauto. simpl_env. auto.
        - eapply Par_Pi with (L := union L (dom (W1 ++ W2 ++ W3))); eauto.
          intros. rewrite app_assoc.
          eapply H1; eauto. simpl_env. auto.
        - move: (Rename_exists (union (dom (W1 ++ W2 ++ W3)) (fv_tm_tm_tm p))
              (axiom_pattern H) (Rename_lc_2 H3)) => h.
          inversion h as [p0 [b0 [D0 h']]].
          assert (tm_pattern_agree (a_App a' nu a1') p0).
           { eapply tm_pattern_agree_rename_inv_1.
           eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match; eauto.
           eauto. eauto.
           }
          eapply Par_AxiomApp; eauto.
          replace a2 with (matchsubst (a_App a' nu a1') p0 b0).
          apply matchsubst_fun_ind.
          auto. eapply Rename_lc_4; eauto. auto.
          move: (axiom_body_fv_in_pattern H) => h1.
          apply Par_roleing_tm_snd in H1. apply rctx_fv in H1.
          apply Par_roleing_tm_snd in H2. apply rctx_fv in H2.
          eapply MatchSubst_Rename_preserve.
          eapply tm_pattern_agree_rename_inv_2.
          eapply MatchSubst_match; eauto. eauto. eauto. eapply H3.
          simpl. clear - H1 H2 h1. apply union_s_m.
          eapply Subset_trans. eapply AtomSetProperties.union_subset_3; eauto.
          rewrite dom_app. rewrite dom_app. apply union_s_m. eauto.
          rewrite dom_app. eauto. eapply AtomSetProperties.union_subset_3; eauto.
          simpl. clear - H1 H2 h1. apply union_s_m.
          eapply AtomSetProperties.union_subset_3; eauto.
          eapply AtomSetProperties.union_subset_3; eauto.
          eapply uniq_atoms_toplevel; eauto.
          apply matchsubst_fun_ind. auto. eapply Rename_lc_4; eauto.
          auto. auto.
        - move: (Rename_exists (union (dom (W1 ++ W2 ++ W3)) (fv_tm_tm_tm p))
              (axiom_pattern H) (Rename_lc_2 H2)) => h.
          inversion h as [p0 [b0 [D0 h']]].
          assert (tm_pattern_agree (a_CApp a' g_Triv) p0).
           { eapply tm_pattern_agree_rename_inv_1.
           eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match; eauto.
           eauto. eauto.
           }
          eapply Par_AxiomCApp; eauto.
          replace a2 with (matchsubst (a_CApp a' g_Triv) p0 b0).
          apply matchsubst_fun_ind.
          auto. eapply Rename_lc_4; eauto. auto.
          move: (axiom_body_fv_in_pattern H) => h1.
          apply Par_roleing_tm_snd in H1. apply rctx_fv in H1.
          eapply MatchSubst_Rename_preserve.
          eapply tm_pattern_agree_rename_inv_2.
          eapply MatchSubst_match; eauto. eauto. eauto. eapply H2.
          simpl. clear - H1 h1. apply union_s_m.
          eapply Subset_trans. rewrite union_empty_r. eauto.
          rewrite dom_app. rewrite dom_app. apply union_s_m. eauto.
          rewrite dom_app. eauto. eapply AtomSetProperties.union_subset_3; eauto.
          simpl. clear - H1 h1. apply union_s_m.
          rewrite union_empty_r. auto.
          eapply AtomSetProperties.union_subset_3; auto.
          eapply uniq_atoms_toplevel; eauto.
          apply matchsubst_fun_ind. auto. eapply Rename_lc_4; eauto.
          auto. auto.
Qed.

(* ------------------------------------------ *)

(* Synatactic properties about parallel reduction. (Excluding confluence.) *)

(* ------------------------------------------ *)


(* TODO: move these definitions to the OTT file. *)

Lemma multipar_app_rctx : forall W1 W2 W3 a a' R, uniq (W1 ++ W2 ++ W3) ->
                     multipar (W1 ++ W3) a a' R ->
                     multipar (W1 ++ W2 ++ W3) a a' R.
Proof. intros W1 W2 W3 a a' R U H. generalize dependent W2.
       dependent induction H; intros; eauto.
        - econstructor. eapply roleing_app_rctx; eauto.
        - econstructor; eauto. apply par_app_rctx; auto.
Qed.

Definition joins W a b R := exists c, multipar W a c R /\ multipar W b c R.

(* FIXME: find a good place for this tactic. *)
(* cannot move this to ett_ind.v because need Toplevel_lc ??? *)
Ltac lc_toplevel_inversion :=
  match goal with
  | [ b : binds ?F _ toplevel |- _ ] =>
    apply Toplevel_lc in b; inversion b; auto
end.

Fixpoint var_pat (p : tm) := match p with
   | a_Fam F => nil
   | a_App p1 nu (a_Var_f x) => (x,app_role nu) :: var_pat p1
   | a_App p1 _ _ => var_pat p1
   | a_CApp p1 g_Triv => var_pat p1
   | _ => nil
   end.

Lemma multipar_roleing_tm_fst: forall W a a' R, multipar W a a' R ->
                                               roleing W a R.
Proof. intros. induction H. auto. eapply Par_roleing_tm_fst; eauto.
Qed.

Lemma multipar_roleing_tm_snd : forall W a a' R, multipar W a a' R ->
                                               roleing W a' R.
Proof. intros. induction H; auto.
Qed.

Lemma Par_rctx_uniq : forall W a a' R, Par W a a' R -> uniq W.
Proof. intros. eapply rctx_uniq. eapply Par_roleing_tm_fst; eauto.
Qed.

Lemma multipar_rctx_uniq: forall W a a' R, multipar W a a' R -> uniq W.
Proof. intros. eapply rctx_uniq. eapply multipar_roleing_tm_fst; eauto.
Qed.

Lemma par_multipar: forall W a a' R, Par W a a' R ->
                                         multipar W a a' R.
Proof. intros. eapply mp_step. eauto. constructor.
       eapply Par_roleing_tm_snd; eauto 1.
Qed.

Hint Resolve Par_roleing_tm_fst Par_roleing_tm_snd : roleing.

(* ------------------------------------------------------------- *)

Lemma Par_sub: forall W a a' R1 R2, Par W a a' R1 -> SubRole R1 R2 ->
                                      Par W a a' R2.
Proof. intros W a a' R1 R2 H SR. generalize dependent R2.
       induction H; intros; eauto. econstructor.
       eapply roleing_sub; eauto.
Qed.

Lemma multipar_sub : forall W a a' R1 R2, multipar W a a' R1 ->
                     SubRole R1 R2 -> multipar W a a' R2.
Proof. intros. induction H. econstructor. eapply roleing_sub; eauto.
       econstructor; eauto. eapply Par_sub; eauto.
Qed.

Lemma subst1 : forall b W W' a a' R1 R2 x, Par W' a a' R1 ->
               roleing (W ++ [(x,R1)] ++ W') b R2 ->
               Par (W ++ W') (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b) R2.
Proof.
  intros b W W' a a' R1 R2 x PAR RJ.
  dependent induction RJ; intros; simpl; auto.
   - constructor. constructor. eapply uniq_remove_mid; eauto.
   - constructor. constructor. eapply uniq_remove_mid; eauto.
   - destruct (x0 == x); auto.
     + subst. assert (P:R = R1).
       eapply binds_mid_eq; eauto. subst. replace W with (nil ++ W); eauto.
       rewrite <- app_assoc. eapply par_app_rctx.
       simpl_env. eapply uniq_remove_mid; eauto.
       simpl_env; eauto. eapply Par_sub; eauto.
     + econstructor. econstructor. eapply uniq_remove_mid; eauto.
       eapply binds_remove_mid; eauto. auto.
   - eapply Par_Abs with (L := union (singleton x) L).
     intros x0 H1.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc1; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc2; eauto.
     rewrite app_assoc. eapply H0; eauto.
   - econstructor; eauto.
   - eauto.
   - eapply Par_Pi with (L := union (singleton x) L); eauto.
     intros x0 h1.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc1; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc2; eauto.
     rewrite app_assoc. eapply H0; eauto.
   - eapply Par_CPi with (L := union L (singleton x)); eauto.
     intros c h1.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply Par_lc1; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply Par_lc2; eauto.
     eapply H0; eauto.
   - eapply Par_CAbs with (L := union L (singleton x)); eauto.
     intros c h1.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply Par_lc1; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply Par_lc2; eauto.
     eapply H0; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
   - eapply Par_Pattern; eauto.
Qed.

Lemma open1 : forall b W L a a' R, Par W a a' R
  -> (forall x, x `notin` L -> roleing W (open_tm_wrt_tm b (a_Var_f x)) R)
  -> Par W (open_tm_wrt_tm b a) (open_tm_wrt_tm b a') R.
Proof.
  intros.
  pick fresh x.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ a')] (tm_subst_tm_tm_intro x); auto.
  replace W with (nil ++ W); auto. eapply subst1; eauto.
  apply roleing_app_rctx; simpl_env.
  constructor; auto. eapply Par_rctx_uniq; eauto.
  auto.
Qed.

Lemma subst2 : forall b W W' a a' R R1 x,
          Par (W ++ [(x,R1)] ++ W') a a' R ->
          roleing W' b R1 ->
          Par (W ++ W') (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a') R.
Proof.
  intros b W W' a a' R R1 x PAR E.
  dependent induction PAR; simpl.
  all: eauto using tm_subst_tm_tm_lc_tm.
  all: autorewrite with subst_open; eauto.
  all: try eapply roleing_lc; eauto.
  - econstructor. eapply subst_tm_roleing; eauto.
  - eapply Par_Abs with (L := union L (singleton x)).
    intros x0 H1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply roleing_lc; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply roleing_lc; eauto.
    rewrite app_assoc. eapply H0. auto. simpl_env; auto.
    auto.
  - eapply Par_Pi with (L := union L (singleton x)); eauto.
    intros x0 H2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply roleing_lc; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply roleing_lc; eauto.
    rewrite app_assoc. eapply H0. auto. simpl_env; auto.
    auto.
  - eapply Par_CAbs with (L := union L (singleton x)).
    intros x0 H1.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply roleing_lc; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply roleing_lc; eauto.
    eapply H0. auto. eauto. auto.
  - eapply Par_CPi with (L := union L (singleton x)); eauto.
    intros x0 H4.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply roleing_lc; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply roleing_lc; eauto.
    eapply H0. auto. eauto. auto.
  - move: (toplevel_inversion H) => h.
    inversion h as [W1 [G [B [Q1 [_ [Q2 _]]]]]].
    apply pat_ctx_rctx in Q1. simpl in Q1. subst. apply rctx_fv in Q2.
    simpl in Q2. rewrite tm_subst_tm_tm_fresh_eq. fsetdec. eauto.
  - inversion H0.
    assert (Q: lc_tm b). {eapply roleing_lc; eauto. }
    eapply Par_AxiomApp; eauto.
    split. eapply tm_subpattern_agree_subst_tm; eauto.
    intro. apply H5. eapply tm_pattern_agree_unsubst_tm.
    eapply tm_subpattern_agree_tm. eauto. eauto.
    eapply Rename_narrow. eauto.
    clear. apply AtomSetProperties.union_subset_4. rewrite dom_app.
    rewrite dom_app. apply AtomSetProperties.union_subset_5. simpl. eauto.
    replace (a_App (tm_subst_tm_tm b x a') nu (tm_subst_tm_tm b x a1'))
      with (tm_subst_tm_tm b x (a_App a' nu a1')) by auto.
    apply MatchSubst_subst_tm; auto.
    eapply MatchSubst_match; eauto.
    move: (axiom_body_fv_in_pattern H) => h.
    eapply Rename_inter_sub_empty. eauto.
    apply Subset_union_left. rewrite dom_app. apply Subset_union_right.
    rewrite dom_app. apply union_s_m. simpl. eauto. eapply rctx_fv; eauto.
    apply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern; eauto. eapply Rename_new_body_fv; eauto.
  - inversion H0.
    assert (Q: lc_tm b). {eapply roleing_lc; eauto. }
    eapply Par_AxiomCApp; eauto.
    split. eapply tm_subpattern_agree_subst_tm; eauto.
    intro. apply H5. eapply tm_pattern_agree_unsubst_tm.
    eapply tm_subpattern_agree_tm. eauto. eauto.
    eapply Rename_narrow. eauto.
    clear. apply AtomSetProperties.union_subset_4. rewrite dom_app.
    rewrite dom_app. apply AtomSetProperties.union_subset_5. simpl. eauto.
    replace (a_CApp (tm_subst_tm_tm b x a') g_Triv)
      with (tm_subst_tm_tm b x (a_CApp a' g_Triv)) by auto.
    apply MatchSubst_subst_tm; auto.
    eapply MatchSubst_match; eauto.
    move: (axiom_body_fv_in_pattern H) => h.
    eapply Rename_inter_sub_empty. eauto.
    apply Subset_union_left. rewrite dom_app. apply Subset_union_right.
    rewrite dom_app. apply union_s_m. simpl. eauto. eapply rctx_fv; eauto.
    apply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern; eauto. eapply Rename_new_body_fv; eauto.
  - assert (lc_tm b). {eapply roleing_lc; eauto. }
    eapply Par_PatternTrue; eauto. apply CasePath_subst_tm; auto.
    apply ApplyArgs_subst_tm; auto.
  - assert (lc_tm b). {eapply roleing_lc; eauto. }
    eapply Par_PatternFalse; eauto.
    eapply Value_tm_subst_tm_tm; eauto.
    intro. apply H0. eapply CasePath_Value_unsubst_tm; eauto.
Qed.

Lemma subst3 : forall b b' W W' a a' R R1 x,
          Par (W ++ [(x,R1)] ++ W') a a' R ->
          Par W' b b' R1 ->
          Par (W ++ W') (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a') R.
Proof.
  intros.
  dependent induction H; simpl; eauto 2; roleing_inversion; eauto 4.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - eapply subst1; eauto.
  - eapply Par_Abs with (L := union L (singleton x)).
    intros x0 H2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc1; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc2; eauto.
    rewrite app_assoc. eapply H0. auto. simpl_env; auto.
    auto.
  - eapply Par_Pi with (L := union (singleton x) L); eauto.
    intros x0 h3.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc1; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply Par_lc2; eauto.
    rewrite app_assoc. eapply H1; eauto. simpl_env; auto.
  - move: (axiom_body_fv_in_pattern H) => h. simpl in h.
    rewrite tm_subst_tm_tm_fresh_eq. fsetdec. eauto.
  - inversion H0.
    assert (Q: lc_tm b). {eapply Par_lc1; eauto. }
    assert (Q': lc_tm b'). {eapply Par_lc2; eauto. }
    eapply Par_AxiomApp; eauto.
    split. eapply tm_subpattern_agree_subst_tm; eauto.
    intro. apply H8. eapply tm_pattern_agree_unsubst_tm.
    eapply tm_subpattern_agree_tm. eauto. eauto.
    eapply Rename_narrow. eauto.
    clear. apply AtomSetProperties.union_subset_4. rewrite dom_app.
    rewrite dom_app. apply AtomSetProperties.union_subset_5. simpl. eauto.
    replace (a_App (tm_subst_tm_tm b' x a') nu (tm_subst_tm_tm b' x a1'))
      with (tm_subst_tm_tm b' x (a_App a' nu a1')) by auto.
    apply MatchSubst_subst_tm; auto.
    eapply MatchSubst_match; eauto.
    move: (axiom_body_fv_in_pattern H) => h.
    eapply Rename_inter_sub_empty. eauto.
    apply Subset_union_left. rewrite dom_app. apply Subset_union_right.
    rewrite dom_app. apply union_s_m. simpl. eauto. eapply rctx_fv; eauto.
    eapply Par_roleing_tm_snd; eauto.
    apply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern; eauto. eapply Rename_new_body_fv; eauto.
  - inversion H0.
    assert (Q: lc_tm b). {eapply Par_lc1; eauto. }
    assert (Q': lc_tm b'). {eapply Par_lc2; eauto. }
    eapply Par_AxiomCApp; eauto.
    split. eapply tm_subpattern_agree_subst_tm; eauto.
    intro. apply H7. eapply tm_pattern_agree_unsubst_tm.
    eapply tm_subpattern_agree_tm. eauto. eauto.
    eapply Rename_narrow. eauto.
    clear. apply AtomSetProperties.union_subset_4. rewrite dom_app.
    rewrite dom_app. apply AtomSetProperties.union_subset_5. simpl. eauto.
    replace (a_CApp (tm_subst_tm_tm b' x a') g_Triv)
      with (tm_subst_tm_tm b' x (a_CApp a' g_Triv)) by auto.
    apply MatchSubst_subst_tm; auto.
    eapply MatchSubst_match; eauto.
    move: (axiom_body_fv_in_pattern H) => h.
    eapply Rename_inter_sub_empty. eauto.
    apply Subset_union_left. rewrite dom_app. apply Subset_union_right.
    rewrite dom_app. apply union_s_m. simpl. eauto. eapply rctx_fv; eauto.
    eapply Par_roleing_tm_snd; eauto.
    apply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern; eauto. eapply Rename_new_body_fv; eauto.
  - eapply Par_Pattern; eauto.
  - assert (lc_tm b'). {eapply Par_lc2; eauto. }
    eapply Par_PatternTrue; eauto. eapply CasePath_subst_tm; eauto.
    apply ApplyArgs_subst_tm; auto.
  - assert (lc_tm b'). {eapply Par_lc2; eauto. }
    eapply Par_PatternFalse; eauto.
    eapply Value_tm_subst_tm_tm; eauto.
    intro. eapply H3. eapply CasePath_Value_unsubst_tm; eauto.
    Unshelve. all:exact.
Qed.

Lemma subst4 : forall g c W a a' R, lc_co g -> Par W a a' R ->
    Par W (co_subst_co_tm g c a) (co_subst_co_tm g c a') R.
Proof.
  intros g c W a a' R LC Par.
  induction Par; simpl; auto.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - apply Par_Refl. eapply subst_co_roleing; eauto.
  - move: (axiom_body_fv_co H) => h.
    rewrite co_subst_co_tm_fresh_eq. fsetdec. eauto.
  - inversion H0.
    move: (Rename_exists 
     ((dom W) \u (singleton c \u fv_tm_tm_co g) \u fv_tm_tm_tm p)
     (axiom_pattern H) (Rename_lc_2 H1)) => h.
    inversion h as [p1 [b1 [D1 h1]]].
    assert (tm_pattern_agree (a_App a' nu a1') p1).
      { eapply tm_pattern_agree_rename_inv_1.
        eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match; eauto.
        eauto. eauto.
      }
    eapply Par_AxiomApp. eauto.
    split. eapply tm_subpattern_agree_subst_co; eauto.
    intro. apply H5. eapply tm_pattern_agree_unsubst_co.
    eapply tm_subpattern_agree_tm. eauto. eauto. eauto. eauto.
    eapply Rename_narrow. eapply h1. apply union_s_m. auto.
    eauto.
    replace (a_App (co_subst_co_tm g c a') nu (co_subst_co_tm g c a1'))
      with (co_subst_co_tm g c (a_App a' nu a1')) by auto.
    apply MatchSubst_subst_co; auto.
    eapply Rename_inter_sub_empty. eapply h1. eauto.
    eapply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern; eauto.
    apply toplevel_inversion in H. inversion H as [W1 [G [B [_ [_ [Q _]]]]]].
    apply rctx_fv_co in Q. move: (Rename_new_body_fv_co h1 Q) => h2.
    eapply Subset_trans; eauto. eapply Subset_empty_any.
    replace a2 with (matchsubst (a_App a' nu a1') p1 b1).
    apply matchsubst_fun_ind.
    auto. eapply Rename_lc_4; eauto. auto.
    move: (axiom_body_fv_in_pattern H) => h3.
    apply Par_roleing_tm_snd in Par1. apply rctx_fv in Par1.
    apply Par_roleing_tm_snd in Par2. apply rctx_fv in Par2.
    eapply MatchSubst_Rename_preserve.
    eapply tm_pattern_agree_rename_inv_2.
    eapply MatchSubst_match; eauto. eauto. eauto. eapply H1.
    simpl. clear - Par1 Par2 h3. apply union_s_m.
    eapply AtomSetProperties.union_subset_3; eauto.
    eapply Subset_union_right. eapply AtomSetProperties.union_subset_3; eauto.
    simpl. clear - Par1 Par2 h3. apply union_s_m.
    eapply AtomSetProperties.union_subset_3; eauto.
    eapply AtomSetProperties.union_subset_3; eauto.
    eapply uniq_atoms_toplevel; eauto.
    apply matchsubst_fun_ind. auto. eapply Rename_lc_4; eauto.
    auto. auto. auto.
  - inversion H0.
    move: (Rename_exists 
     ((dom W) \u (singleton c \u fv_tm_tm_co g) \u fv_tm_tm_tm p)
     (axiom_pattern H) (Rename_lc_2 H1)) => h.
    inversion h as [p1 [b1 [D1 h1]]].
    assert (tm_pattern_agree (a_CApp a' g_Triv) p1).
      { eapply tm_pattern_agree_rename_inv_1.
        eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match; eauto.
        eauto. eauto.
      }
    eapply Par_AxiomCApp. eauto.
    split. eapply tm_subpattern_agree_subst_co; eauto.
    intro. apply H5. eapply tm_pattern_agree_unsubst_co.
    eapply tm_subpattern_agree_tm. eauto. eauto. eauto.
    eapply Rename_narrow. eauto. apply union_s_m; eauto.
    replace (a_CApp (co_subst_co_tm g c a') g_Triv)
      with (co_subst_co_tm g c (a_CApp a' g_Triv)) by auto.
    apply MatchSubst_subst_co; auto.
    eapply Rename_inter_sub_empty. eauto. eauto.
    apply toplevel_inversion in H. inversion H as [W1 [G [B [_ [_ [Q _]]]]]].
    apply rctx_fv_co in Q. move: (Rename_new_body_fv_co h1 Q) => h2.
    eapply AtomSetProperties.union_subset_3.
    eapply Rename_fv_new_pattern; eauto. eapply Subset_trans; eauto.
    apply Subset_empty_any.
    replace a2 with (matchsubst (a_CApp a' g_Triv) p1 b1).
    apply matchsubst_fun_ind.
    auto. eapply Rename_lc_4; eauto. auto.
    move: (axiom_body_fv_in_pattern H) => h3.
    apply Par_roleing_tm_snd in Par. apply rctx_fv in Par.
    eapply MatchSubst_Rename_preserve.
    eapply tm_pattern_agree_rename_inv_2.
    eapply MatchSubst_match; eauto. eauto. eauto. eapply H1.
    simpl. clear - Par h3. apply union_s_m.
    rewrite union_empty_r. auto.
    eapply Subset_union_right. eapply AtomSetProperties.union_subset_3; eauto.
    simpl. clear - Par h3. apply union_s_m.
    rewrite union_empty_r. auto.
    eapply AtomSetProperties.union_subset_3; eauto.
    eapply uniq_atoms_toplevel; eauto.
    apply matchsubst_fun_ind. auto. eapply Rename_lc_4; eauto.
    auto. auto. auto.
  - eapply Par_PatternTrue; eauto. apply CasePath_subst_co; auto.
    apply ApplyArgs_subst_co; auto.
  - eapply Par_PatternFalse; eauto. eapply Value_co_subst_co_tm; eauto.
    intro. apply H0. eapply CasePath_Value_unsubst_co; eauto.
Qed.

Lemma multipar_subst3 : forall b b' W W' a a' R R1 x,
     multipar (W ++ [(x,R1)] ++ W') a a' R ->
     multipar W' b b' R1 ->
     multipar (W ++ W') (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a') R.
Proof.
  intros b b' W W' a a' R R1 x H1 H2.
  dependent induction H1; auto.
  - dependent induction H2; auto.
    constructor. eapply subst_tm_roleing; eauto.
    apply (@mp_step _ _ _ ((tm_subst_tm_tm b x a))); auto.
    eapply subst3; eauto.
  - dependent induction H2; auto.
    apply (@mp_step _ _ _ (tm_subst_tm_tm a0 x b0)); auto.
    eapply subst3; eauto.
    apply (@mp_step _ _ _ ((tm_subst_tm_tm a0 x b0))); auto.
    eapply subst2; eauto. eapply Par_roleing_tm_fst; eauto.
    apply IHmultipar; auto.
    econstructor; eauto.
Qed.

Lemma multipar_subst4 : forall W b x, lc_co b ->
    forall a a' R, multipar W a a' R ->
    multipar W (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros W b x H a a' R H0.
  dependent induction H0; eauto.
  constructor. eapply subst_co_roleing; eauto.
  apply (@mp_step _ _ _ (co_subst_co_tm b x b0)); auto.
  apply subst4; auto.
Qed.

Lemma roleing_tm_open_tm_wrt_tm: forall W a R x, roleing W a R -> roleing W (open_tm_wrt_tm a (a_Var_f x)) R.
Proof.
  intros W a R x H.
  pose K := roleing_lc H.
  rewrite open_tm_wrt_tm_lc_tm; eauto.
Qed.

Hint Resolve roleing_tm_open_tm_wrt_tm : roleing.


Lemma Par_Pi_exists: ∀ x W rho (A B A' B' : tm) R',
    x `notin` fv_tm_tm_tm B -> Par W A A' R'
    → Par ([(x,Nom)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) B' R'
    → Par W (a_Pi rho A B) (a_Pi rho A' (close_tm_wrt_tm x B')) R'.
Proof.
  intros x W rho A B A' B' R' H H0 H1.
  apply (Par_Pi (union (singleton x) (union (dom W) (fv_tm_tm_tm B)))); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
  replace (x0 ~ Nom ++ W) with (nil ++ [(x0,Nom)] ++ W); auto.
  assert (uniq ([(x,Nom)] ++ W)). {eapply Par_rctx_uniq; eauto. }
  eapply subst2; eauto.
  simpl_env. apply par_app_rctx; eauto 1. solve_uniq.
  econstructor. solve_uniq. auto. auto.
Qed.

Lemma Par_CPi_exists:  ∀ c W (A B a A' B' a' T T': tm) R R',
       c `notin` fv_co_co_tm a -> Par W A A' R
       → Par W B B' R -> Par W T T' Rep
         → Par W (open_tm_wrt_co a (g_Var_f c)) (a') R'
         → Par W (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) (close_tm_wrt_co c a')) R'.
Proof.
  intros c W A B a A' B' a' T T' R R' H H0 H1 H2 H3.
  eapply (Par_CPi (singleton c)); eauto.
  intros c0 h3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.


Lemma Par_Abs_exists: ∀ x W rho R' (a a' : tm),
    x `notin` fv_tm_tm_tm a
    → Par ([(x,Nom)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) a' R'
    → Par W (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')) R'.
Proof.
  intros x W rho R' a a' hi0 H0.
  apply (Par_Abs (union (singleton x) (dom W))); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x a (a_Var_f x0)); auto.
  replace (x0 ~ Nom ++ W) with (nil ++ [(x0,Nom)] ++ W); auto.
  assert (uniq ([(x,Nom)] ++ W)). {eapply Par_rctx_uniq; eauto. }
  eapply subst2; eauto.
  simpl_env. apply par_app_rctx; eauto 1.
  solve_uniq. econstructor. solve_uniq. auto. auto.
Qed.

Lemma Par_CAbs_exists: forall c W (a a': tm) R,
       c `notin` fv_co_co_tm a
       -> Par W (open_tm_wrt_co a (g_Var_f c)) a' R
       → Par W (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')) R.
Proof.
  intros c W a a' R H H0.
  apply (Par_CAbs (singleton c)); auto.
  intros c0 H3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.

Lemma Par_open_tm_wrt_co_preservation: forall W B1 B2 c R,
  Par W (open_tm_wrt_co B1 (g_Var_f c)) B2 R ->
  exists B', B2 = open_tm_wrt_co B' (g_Var_f c)
    /\ Par W (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)) R.
Proof.
  intros W B1 B2 c R H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma Par_open_tm_wrt_tm_preservation: forall W B1 B2 x R,
  Par W (open_tm_wrt_tm B1 (a_Var_f x)) B2 R ->
  exists B', B2 = open_tm_wrt_tm B' (a_Var_f x)
    /\ Par W (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros W B1 B2 x R H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_Pi_exists: ∀ x W rho (A B A' B' : tm) R',
       x `notin` fv_tm_tm_tm B ->
       multipar W A A' R'
       → multipar ([(x,Nom)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) B' R'
       → multipar W (a_Pi rho A B) (a_Pi rho A' (close_tm_wrt_tm x B')) R'.
Proof.
  intros x W rho A B A' B' R' e H H0.
  dependent induction H; eauto.
  - dependent induction H0; eauto.
    erewrite close_tm_wrt_tm_open_tm_wrt_tm; eauto.
    constructor. eapply roleing_Pi_some_any; eauto.
    apply mp_step with (b := a_Pi rho a (close_tm_wrt_tm x b)); auto.
    + eapply Par_Pi_exists; eauto.
    + apply IHmultipar; auto.
      * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
        fsetdec.
      * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - apply (@mp_step _ _ _ (a_Pi rho b B)); auto.
    apply (Par_Pi (union (singleton x) (union (dom W) (fv_tm_tm_tm B)))).
    auto. intros. econstructor.
    assert (uniq ([(x,Nom)] ++ W)). {eapply multipar_rctx_uniq; eauto. }
    rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
    replace (x0 ~ Nom ++ W) with (nil ++ [(x0,Nom)] ++ W); auto.
    eapply subst_tm_roleing. simpl_env. apply roleing_app_rctx.
    solve_uniq. eapply multipar_roleing_tm_fst; eauto.
    econstructor. solve_uniq. eauto. eauto.
Qed.


Lemma multipar_Pi_A_proj: ∀ W rho (A B A' B' : tm) R',
    multipar W (a_Pi rho A B) (a_Pi rho A' B') R' ->
    multipar W A A' R'.
Proof.
  intros W rho A B A' B' R' h1.
  dependent induction h1.
  - inversion H. subst. constructor. auto.
  - inversion H. subst. eapply IHh1; eauto.
    apply mp_step with (b := A'0). auto.
    eapply IHh1; eauto.
Qed.

Lemma multipar_Pi_B_proj: ∀ W rho (A B A' B' : tm) R',
    multipar W (a_Pi rho A B) (a_Pi rho A' B') R' →
    exists L, forall x, x `notin` L ->
      multipar ([(x,Nom)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R'.
Proof.
  intros W rho A B A' B' R' h1.
  dependent induction h1; eauto.
  - inversion H. subst. exists L. intros.
    constructor. replace [(x,Nom)] with (x ~ Nom). auto. auto.
  - inversion H; subst.
    eapply IHh1; eauto.
    destruct (IHh1 rho A'0 B'0 A' B') as [L0 h0]; auto.
    exists (L \u L0); eauto.
Qed.


Lemma multipar_CPi_exists:  ∀ c W (A B a T A' B' a' T': tm) R R',
       c `notin` fv_co_co_tm a ->
       multipar W A A' R →
       multipar W B B' R ->
       multipar W T T' Rep →
       multipar W (open_tm_wrt_co a (g_Var_f c)) a' R' →
       multipar W (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) (close_tm_wrt_co c a')) R'.
Proof.
  intros c W A B a T A' B' a' T' R R' e H H0 H2 H1.
  dependent induction H; eauto 1.
  - dependent induction H0; eauto 1.
    + dependent induction H1; eauto 1.
      * dependent induction H2; eauto 1.
        rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
        constructor. econstructor; eauto 1.
        intros. rewrite (co_subst_co_tm_intro c). auto.
        apply subst_co_roleing. auto. auto.
        apply mp_step with (b:= (a_CPi (Eq a0 a1 b R) a)); eauto.
        econstructor; eauto 2. intros. constructor.
        rewrite (co_subst_co_tm_intro c). auto.
        apply subst_co_roleing. auto. auto.
      * eapply mp_step with (b:= (a_CPi (Eq a0 a1 T R) (close_tm_wrt_co c b))); eauto.
        -- apply Par_CPi_exists; auto 2. constructor.
           eapply multipar_roleing_tm_fst; eauto.
        -- apply IHmultipar; eauto.
           ++ rewrite fv_co_co_tm_close_tm_wrt_co_rec.
              fsetdec.
           ++ rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
      + eapply mp_step with (b:= (a_CPi (Eq a0 b T R) a)); eauto.
        -- eapply (Par_CPi (singleton c)); eauto 2.
           constructor. eapply multipar_roleing_tm_fst; eauto.
           intros. constructor. rewrite (co_subst_co_tm_intro c). auto.
           apply subst_co_roleing. auto. eapply multipar_roleing_tm_fst; eauto.
  - apply mp_step with (b:= (a_CPi (Eq b B T R) a)); auto.
     eapply (Par_CPi (singleton c)); eauto.
     constructor. eapply multipar_roleing_tm_fst; eauto.
     constructor. eapply roleing_sub. eapply multipar_roleing_tm_fst; eauto.
     auto. intros. constructor. rewrite (co_subst_co_tm_intro c). auto.
     apply subst_co_roleing. auto.
     eapply multipar_roleing_tm_fst; eauto.
     Unshelve. all:eauto. apply (fv_co_co_tm a). apply (fv_co_co_tm a).
Qed.


Lemma multipar_CPi_B_proj:  ∀ W (A B a A' B' a' T T': tm) R1 R2 R',
    multipar W (a_CPi (Eq A B T R1) a) (a_CPi (Eq A' B' T' R2) a') R' →
    exists L, forall c, c `notin` L ->
      multipar W (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)) R'.
Proof.
  intros W A B a A' B' a' T T' R1 R2 R' h1.
  dependent induction h1; eauto.
  - inversion H. subst. exists L. intros.
    constructor. auto.
  - inversion H; subst.
    eapply IHh1; eauto.
    destruct (IHh1 _ _ _ _ _ _ _ _ _ _ ltac:(auto) ltac:(auto)) as [L0 h0]; auto.
    exists (L \u L0); eauto.
Qed.

Lemma multipar_CPi_phi_proj:  ∀ W (A B a A' B' a' T T': tm) R R1 R',
    multipar W (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R1) a') R' ->
    R = R1
      /\ multipar W A A' R
      /\ multipar W B B' R
      /\ multipar W T T' Rep.
Proof.
  intros W A B a A' B' a' T T' R R1 R' H.
  dependent induction H; eauto.
  - inversion H; subst. split. auto.
    repeat split. all:econstructor. all:eapply roleing_sub; eauto.
  - inversion H; subst.
    eapply IHmultipar; eauto.
    destruct (IHmultipar _ _ _ _ _ _ _ _ _ _ ltac:(auto) ltac:(auto))
    as [EQ [H1 [H2 H3]]]. subst.
    repeat split.
    auto.
    apply mp_step with (b := a'0); auto.
    apply mp_step with (b := b'); auto.
    apply mp_step with (b := A'0); auto.
Qed.


Lemma multipar_Abs_exists: ∀ x W rho R' (a a' : tm),
       x `notin` fv_tm_tm_tm a →
       multipar ([(x,Nom)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) a' R' →
       multipar W (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')) R'.
Proof.
  intros x W rho R' B B' e H.
  dependent induction H; eauto 2.
  - autorewrite with lngen. constructor.
    assert (uniq ([(x,Nom)] ++ W)). {eapply rctx_uniq; eauto. }
    apply role_a_Abs with (L := union (singleton x) (dom W)).
    intros. rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
    replace (x0 ~ Nom ++ W) with (nil ++ [(x0,Nom)] ++ W); auto.
    apply subst_tm_roleing with (R1 := Nom). simpl_env. apply roleing_app_rctx.
    solve_uniq. auto. econstructor; auto. solve_uniq.
  - assert (Par W (a_UAbs rho B) (a_UAbs rho (close_tm_wrt_tm x b)) R).
    eapply (Par_Abs_exists); auto.
    assert (multipar W (a_UAbs rho (close_tm_wrt_tm x b))
                       (a_UAbs rho (close_tm_wrt_tm x c)) R).
    { apply IHmultipar; auto.
    * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
      fsetdec.
    * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto. }
    eapply mp_step; eauto.
Qed.

Lemma multipar_CAbs_exists: forall c W (a a': tm) R,
       c `notin` fv_co_co_tm a →
       multipar W (open_tm_wrt_co a (g_Var_f c)) a' R →
       multipar W (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')) R.
Proof.
  intros c W a a' R e H.
  dependent induction H; eauto 1.
  - rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
    econstructor. apply role_a_CAbs with (L := fv_co_co_tm a).
    intros. rewrite (co_subst_co_tm_intro c); auto.
    apply subst_co_roleing. auto. auto.
  - apply mp_step with (b := ((a_UCAbs (close_tm_wrt_co c b)))); eauto.
    apply Par_CAbs_exists; auto.
    apply IHmultipar; eauto.
    rewrite fv_co_co_tm_close_tm_wrt_co_rec. fsetdec.
    rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
Qed.

Lemma multipar_open_tm_wrt_co_preservation: forall W B1 B2 c R,
  multipar W (open_tm_wrt_co B1 (g_Var_f c)) B2 R ->
  exists B', B2 = open_tm_wrt_co B' (g_Var_f c)
    /\ multipar W (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)) R.
Proof.
  intros W B1 B2 c R H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_open_tm_wrt_tm_preservation: forall W B1 B2 R x,
  multipar W (open_tm_wrt_tm B1 (a_Var_f x)) B2 R ->
  exists B', B2 = open_tm_wrt_tm B' (a_Var_f x)
    /\ multipar W (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros W B1 B2 R x H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma RolePath_roles_agree : forall F p b A R Rs a Rs',
      binds F (Ax p b A R Rs) toplevel-> RolePath a F Rs' ->
      Rs = tm_app_roles a ++ Rs'.
Proof. intros. induction H0; simpl; eauto. axioms_head_same.
       axioms_head_same. auto. rewrite <- app_assoc. simpl.
       eauto.
Qed.

Lemma MatchSubst_par : forall a1 p b b' b'' W W' a2 R F p1 b1 A R1 Rs,
  MatchSubst a1 p b b' -> ~tm_pattern_agree a1 p1 ->
  tm_subpattern_agree a1 p1 -> binds F (Ax p1 b1 A R1 Rs) toplevel ->
  roleing (W' ++ rev (combine (vars_Pattern p) (pat_app_roles p))) b R ->
  Par W a1 a2 R -> MatchSubst a2 p b b'' ->
  uniq (W' ++ (combine (vars_Pattern p) (pat_app_roles p)) ++ W) ->
  Par (W' ++ W) b' b'' R.
Proof. intros. generalize dependent a2. generalize dependent b''.
       generalize dependent p1. generalize dependent W. generalize dependent W'.
       induction H; intros; eauto.
        - inversion H5; subst. simpl in H3. simpl in H6.
          rewrite app_nil_r in H3. replace (W' ++ W) with (W' ++ W ++ nil).
          eapply par_app_rctx. simpl_env. auto. simpl_env; eauto.
          simpl_env. auto.
        - inversion H7; subst. simpl in H3. erewrite combine_app in H3.
          rewrite rev_app_distr in H3. simpl in H3. simpl in H6.
          erewrite combine_app in H6. simpl in H6.
          inversion H5; subst.
          + inversion H13; subst.
            eapply subst2 with (R1 := R0); auto. rewrite app_assoc.
            eapply IHMatchSubst; eauto. rewrite <- app_assoc. auto.
            clear - H6. solve_uniq.
            intro. eapply tm_subpattern_agree_app_contr; eauto.
            eapply tm_subpattern_agree_sub_app; eauto.
          + eapply subst3 with (R1 := R0); auto.
            rewrite app_assoc. eapply IHMatchSubst; eauto.
            rewrite <- app_assoc. auto. clear - H6. solve_uniq.
            intro. eapply tm_subpattern_agree_app_contr; eauto.
            eapply tm_subpattern_agree_sub_app; eauto.
          + pattern_head_tm_agree. simpl in U1. inversion H12.
            rename U1 into U2. pattern_head_tm_agree. rewrite U2 in U1.
            inversion U1; subst. axioms_head_same. assert False.
            apply H1. eapply tm_pattern_agree_cong.
            eapply tm_pattern_agree_rename_inv_2.
            eapply MatchSubst_match. eapply H21. eauto.
            econstructor. eapply tm_tm_agree_sym.
            eapply pattern_like_tm_par; eauto.
            eapply Par_lc2; eauto. eapply Par_lc1; eauto.
            contradiction.
        - inversion H7; subst. simpl in H3. simpl in H6. inversion H5; subst.
          + inversion H15; subst.
            eapply IHMatchSubst; eauto. intro.
            eapply tm_subpattern_agree_app_contr; eauto.
            eapply tm_subpattern_agree_sub_app; eauto.
          + assert False. eapply pattern_like_tm_par.
            eapply H16. eauto. eapply tm_subpattern_agree_sub_app; eauto.
            intro. eapply tm_subpattern_agree_app_contr; eauto. eauto.
            contradiction.
          + eapply IHMatchSubst; eauto.
            intro. eapply tm_subpattern_agree_app_contr; eauto.
            eapply tm_subpattern_agree_sub_app; eauto.
          + pattern_head_tm_agree. simpl in U1. inversion H14.
            rename U1 into U2. pattern_head_tm_agree. rewrite U2 in U1.
            inversion U1; subst. axioms_head_same. assert False.
            apply H1. eapply tm_pattern_agree_cong.
            eapply tm_pattern_agree_rename_inv_2.
            eapply MatchSubst_match. eapply H21. eauto.
            econstructor. eapply tm_tm_agree_sym.
            eapply pattern_like_tm_par; eauto.
            eapply Par_lc2; eauto. eapply Par_lc1; eauto.
            contradiction.
        - inversion H5; subst. simpl in H3. simpl in H6. inversion H4; subst.
          + inversion H11; subst.
            eapply IHMatchSubst; eauto. intro.
            eapply tm_subpattern_agree_capp_contr; eauto.
            eapply tm_subpattern_agree_sub_capp; eauto.
          + assert False. eapply pattern_like_tm_par.
            eapply H11. eauto. eapply tm_subpattern_agree_sub_capp; eauto.
            intro. eapply tm_subpattern_agree_capp_contr; eauto. eauto.
            contradiction.
          + eapply IHMatchSubst; eauto.
            intro. eapply tm_subpattern_agree_capp_contr; eauto.
            eapply tm_subpattern_agree_sub_capp; eauto.
          + pattern_head_tm_agree. simpl in U1. inversion H10.
            rename U1 into U2. pattern_head_tm_agree. rewrite U2 in U1.
            inversion U1; subst. axioms_head_same. assert False.
            apply H0. eapply tm_pattern_agree_cong.
            eapply tm_pattern_agree_rename_inv_2.
            eapply MatchSubst_match. eapply H13. eauto.
            econstructor. eapply tm_tm_agree_sym.
            eapply pattern_like_tm_par; eauto.
            contradiction.
Qed.


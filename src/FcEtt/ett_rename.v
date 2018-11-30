Require Export FcEtt.imports.
Require Import ett_ott.
Require Import ett_inf.
Require Import ett_match.

Inductive pattern_renamed : tm -> tm -> available_props ->
                                        available_props -> Prop :=
 | pattern_renamed_Base : forall (F:const) (D:available_props),
     pattern_renamed (a_Fam F) (a_Fam F) D  AtomSetImpl.empty
 | pattern_renamed_AppRel : forall (p1:tm) (R:role) (x:tmvar) (p2:tm)
                                  (y:tmvar) (D D':available_props),
     pattern_renamed p1 p2 D D' -> ~ AtomSetImpl.In  y (D  \u  D') ->
     pattern_renamed (a_App p1 (Role R) (a_Var_f x))
                     (a_App p2 (Role R) (a_Var_f y)) D  (singleton  y  \u  D')
 | pattern_renamed_AppIrrel : forall (p1 p2:tm) (D D':available_props),
     pattern_renamed p1 p2 D D' ->
     pattern_renamed (a_App p1 (Rho Irrel) a_Bullet)
                     (a_App p2 (Rho Irrel) a_Bullet) D D'
 | pattern_renamed_CApp : forall (p1 p2:tm) (D D':available_props),
     pattern_renamed p1 p2 D D' ->
     pattern_renamed (a_CApp p1 g_Triv) (a_CApp p2 g_Triv) D D'.

Hint Constructors pattern_renamed.

Fixpoint tm_var_pairs (a p : tm) : list (tm * var) :=
   match (a,p) with
 | (a_Fam F, a_Fam F') => []
 | (a_App a1 (Role R) a2, a_App p1 (Role R') (a_Var_f x)) =>
                                       tm_var_pairs a1 p1 ++ [(a2,x)]
 | (a_App a (Rho Irrel) a', a_App p (Rho Irrel) a_Bullet) =>
                                       tm_var_pairs a p
 | (a_CApp a g_Triv, a_CApp p g_Triv) => tm_var_pairs a p
 | (_,_) => []
   end.

Definition chain_subst a p b := fold_left
       (fun b' a'x' => tm_subst_tm_tm a'x'.1 a'x'.2 b') (tm_var_pairs a p) b.

Lemma chain_subst_fv : forall a p b, tm_pattern_agree a p ->
      fv_tm_tm_tm (chain_subst a p b) [<=]
        (AtomSetImpl.diff (fv_tm_tm_tm b) (fv_tm_tm_tm p)) \u (fv_tm_tm_tm a).
Proof. intros. induction H; eauto.
        - pose (P := fv_tm_tm_tm_tm_subst_tm_tm_upper (chain_subst a1 p1 b) a2 x).
          unfold chain_subst in *. simpl. rewrite fold_left_app. simpl.
          eapply Subset_trans. eapply P. fsetdec.
        - unfold chain_subst in *. simpl. fsetdec.
        - unfold chain_subst in *. simpl. fsetdec.
Qed.

Lemma Rename_pattern_renamed : forall p b p' b' D D', Rename p b p' b' D D' ->
      pattern_renamed p p' D D'.
Proof. intros. induction H; eauto.
Qed.

Lemma Rename_chain_subst : forall p b p' b' D D', Rename p b p' b' D D' ->
                           b' = chain_subst p' p b.
Proof. intros. induction H; simpl; eauto.
       unfold chain_subst in *. simpl. rewrite fold_left_app. simpl.
       rewrite <- IHRename. auto.
Qed.

Lemma chain_subst_Rename : forall p b p' D D', pattern_renamed p p' D D' ->
      lc_tm b -> Rename p b p' (chain_subst p' p b) D D'.
Proof. intros. induction H; simpl; eauto. unfold chain_subst in *.
       simpl. rewrite fold_left_app. simpl. eauto.
Qed.

Lemma matchsubst_chain_subst : forall a p b, tm_pattern_agree a p ->
                               matchsubst a p b = chain_subst a p b.
Proof. intros. induction H; simpl; eauto. unfold chain_subst in *. simpl.
       rewrite fold_left_app. simpl. rewrite <- IHtm_pattern_agree. auto.
Qed.

Lemma subst_via : forall a y z,
      (forall b, y `notin` fv_tm_tm_tm b ->
      tm_subst_tm_tm a y (tm_subst_tm_tm (a_Var_f y) z b) =
      tm_subst_tm_tm a z b) /\
      (forall brs, y `notin` fv_tm_tm_brs brs ->
      tm_subst_tm_brs a y (tm_subst_tm_brs (a_Var_f y) z brs) =
      tm_subst_tm_brs a z brs) /\
      (forall g, y `notin` fv_tm_tm_co g ->
      tm_subst_tm_co a y (tm_subst_tm_co (a_Var_f y) z g) =
      tm_subst_tm_co a z g) /\
      (forall phi, y `notin` fv_tm_tm_constraint phi ->
      tm_subst_tm_constraint a y (tm_subst_tm_constraint (a_Var_f y) z phi) =
      tm_subst_tm_constraint a z phi).
Proof. intros. apply tm_brs_co_constraint_mutind; intros; simpl;
       try (simpl in H; try simpl in H1; try simpl in H2; f_equal; eauto; fail).
       destruct (eq_var x z). simpl. rewrite eq_dec_refl. auto.
       simpl. destruct (eq_var x y). subst. simpl in H. fsetdec. auto.
Qed.

Lemma subst_via_tm : forall a y z b, y `notin` fv_tm_tm_tm b ->
      tm_subst_tm_tm a y (tm_subst_tm_tm (a_Var_f y) z b) =
      tm_subst_tm_tm a z b.
Proof. intros. eapply subst_via; eauto.
Qed.

Lemma subst_commute : forall a1 a2 x1 x2, x1 `notin` fv_tm_tm_tm a2 ->
      x2 `notin` fv_tm_tm_tm a1 -> x1 <> x2 ->
      (forall b, tm_subst_tm_tm a2 x2 (tm_subst_tm_tm a1 x1 b) =
      tm_subst_tm_tm a1 x1 (tm_subst_tm_tm a2 x2 b)) /\
      (forall brs, tm_subst_tm_brs a2 x2 (tm_subst_tm_brs a1 x1 brs) =
      tm_subst_tm_brs a1 x1 (tm_subst_tm_brs a2 x2 brs)) /\
      (forall g, tm_subst_tm_co a2 x2 (tm_subst_tm_co a1 x1 g) =
      tm_subst_tm_co a1 x1 (tm_subst_tm_co a2 x2 g)) /\
      (forall phi, tm_subst_tm_constraint a2 x2
       (tm_subst_tm_constraint a1 x1 phi) =
        tm_subst_tm_constraint a1 x1 (tm_subst_tm_constraint a2 x2 phi)).
Proof. intros a1 a2 x1 x2 P Q R.
       apply tm_brs_co_constraint_mutind; intros; simpl; eauto;
       try (f_equal; eauto; fail).
       destruct (eq_var x x1). destruct (eq_var x x2). subst. contradiction.
       subst. simpl. rewrite eq_dec_refl. rewrite tm_subst_tm_tm_fresh_eq; auto.
       destruct (eq_var x x2). subst. simpl. rewrite eq_dec_refl.
       rewrite tm_subst_tm_tm_fresh_eq; auto.
       rewrite tm_subst_tm_tm_fresh_eq; auto.
       rewrite tm_subst_tm_tm_fresh_eq; auto.
Qed.

Lemma subst_commute_tm : forall a1 a2 x1 x2 b, x1 `notin` fv_tm_tm_tm a2 ->
      x2 `notin` fv_tm_tm_tm a1 -> x1 <> x2 ->
      tm_subst_tm_tm a2 x2 (tm_subst_tm_tm a1 x1 b) =
      tm_subst_tm_tm a1 x1 (tm_subst_tm_tm a2 x2 b).
Proof. intros. eapply subst_commute; auto.
Qed.

Lemma chain_subst_subst_commute : forall a p x a' b,
      tm_pattern_agree a p ->
      x `notin` fv_tm_tm_tm a -> x `notin` fv_tm_tm_tm p ->
      AtomSetImpl.inter (fv_tm_tm_tm p) (fv_tm_tm_tm a') [<=] empty ->
      chain_subst a p (tm_subst_tm_tm a' x b) =
      tm_subst_tm_tm a' x (chain_subst a p b).
Proof. intros. generalize dependent b. induction H; intros; simpl; eauto.
        - simpl in H0, H1, H2. unfold chain_subst in *. simpl.
          rewrite fold_left_app. rewrite fold_left_app. simpl.
          rewrite subst_commute_tm. fsetdec. fsetdec. fsetdec.
          rewrite IHtm_pattern_agree. fsetdec. fsetdec. fsetdec. auto.
        - simpl in H0, H1, H2. unfold chain_subst in *. simpl.
          rewrite IHtm_pattern_agree. fsetdec. fsetdec. fsetdec. auto.
        - simpl in H0, H1, H2. unfold chain_subst in *. simpl.
          rewrite IHtm_pattern_agree. fsetdec. fsetdec. fsetdec. auto.
Qed.


Theorem MatchSubst_Rename_preserve : forall p b D D' p1 b1 D1 p2 b2 D2 a a1 a2,
   tm_pattern_agree a p -> Rename p b p1 b1 D D1 -> Rename p b p2 b2 D' D2 ->
   (fv_tm_tm_tm a \u fv_tm_tm_tm p \u fv_tm_tm_tm b) [<=] D ->
   (fv_tm_tm_tm a \u fv_tm_tm_tm p \u fv_tm_tm_tm b) [<=] D' ->
   uniq_atoms_pattern p -> MatchSubst a p1 b1 a1 -> MatchSubst a p2 b2 a2 ->
   a1 = a2.
Proof. intros. generalize dependent p1. generalize dependent b1.
       generalize dependent D. generalize dependent D1. generalize dependent a1.
       generalize dependent a2. generalize dependent p2. generalize dependent b2.
       generalize dependent D'. generalize dependent D2. generalize dependent b.
       induction H; intros.
         - inversion H5. inversion H0. inversion H6. inversion H1. subst. auto.
         - unfold uniq_atoms_pattern in *. simpl in *.
           inversion H5; subst. inversion H7; inversion H1; subst.
           inversion H6; subst.
           assert (L1 : tm_pattern_agree a1 p4).
             { eapply MatchSubst_match; eauto. }
           assert (L2 : tm_pattern_agree a1 p5).
             { eapply MatchSubst_match; eauto. }
           assert (L3 : pattern_renamed p1 p4 D D'0).
             { eapply Rename_pattern_renamed; eauto. }
           assert (L4 : pattern_renamed p1 p5 D' D'1).
             { eapply Rename_pattern_renamed; eauto. }
           pose (P1 := matchsubst_ind_fun H18).
           pose (P2 := matchsubst_ind_fun H20). rewrite <- P1. rewrite <- P2.
           rewrite matchsubst_chain_subst. auto.
           rewrite matchsubst_chain_subst. auto.
           pose (P3 := Rename_chain_subst H16).
           pose (P4 := Rename_chain_subst H27). rewrite P3. rewrite P4.
           pick fresh z.
           assert 
           (HYP : chain_subst a1 p4 (chain_subst p4 p1
                      (tm_subst_tm_tm (a_Var_f z) x b)) =
                  chain_subst a1 p5 (chain_subst p5 p1
                      (tm_subst_tm_tm (a_Var_f z) x b))).
           { apply IHtm_pattern_agree with (b := tm_subst_tm_tm (a_Var_f z) x b)
             (D := D \u singleton z)(D1 := D'0)(p3 := p4)
             (b1 := chain_subst p4 p1 (tm_subst_tm_tm (a_Var_f z) x b))
             (D' := D' \u singleton z)(D2 := D'1)(p2 := p5)
             (b2 := chain_subst p5 p1 (tm_subst_tm_tm (a_Var_f z) x b)).
             unfold uniq_atoms in *.
             eapply uniq_app_1. rewrite map_app in H4. eauto.
             pose (R1 := fv_tm_tm_tm_tm_subst_tm_tm_upper b (a_Var_f z) x).
             simpl in R1. apply Subset_trans with (D2 := fv_tm_tm_tm a1 \u
             fv_tm_tm_tm p1 \u singleton z \u 
             (Metatheory.remove x (fv_tm_tm_tm b))). eapply Subset_union.
             eauto. eapply Subset_union. eauto. auto. fsetdec.
           rewrite <- tm_subst_tm_tm_back_forth with (x := y) (y := z)
          (b := tm_subst_tm_tm (a_Var_f y) x (chain_subst p4 p1 b)).
           rewrite -> subst_via_tm with (y := y) (b := chain_subst p4 p1 b).
           rewrite -> chain_subst_subst_commute with (a' := a_Var_f y) (x := z).
           rewrite -> subst_via_tm with (y := y).
           rewrite <- chain_subst_subst_commute with (a' := a_Var_f z).
         - unfold uniq_atoms_pattern in *. simpl in *.
           inversion H5; subst. inversion H7; inversion H1; subst.
           inversion H6; subst.
           eapply IHtm_pattern_agree with (b := b)(D' := D') (D := D). auto.
           fsetdec. eapply H17. auto. fsetdec. eapply H9. auto.
         - unfold uniq_atoms_pattern in *. simpl in *.
           inversion H0; subst. inversion H5; inversion H1; subst.
           inversion H6; subst.
           eapply IHtm_pattern_agree with (b := b)(D' := D') (D := D). auto.
           fsetdec. eapply H14. auto. fsetdec. eapply H8. auto.
Admitted.

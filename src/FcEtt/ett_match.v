Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.toplevel.
Require Export FcEtt.fix_typing.
Require Import FcEtt.ett_roleing.
Require Import FcEtt.ett_path.
Require Import FcEtt.ext_wf.
Require Import Omega.

(** Patterns, agreement and substitution function **)

Inductive Pattern : tm -> Prop :=
  | Pattern_Fam : forall F, Pattern (a_Fam F)
  | Pattern_AppR : forall a1 R x, Pattern a1 -> Pattern (a_App a1 (Role R) (a_Var_f x))
  | Pattern_IApp : forall a1, Pattern a1 -> Pattern (a_App a1 (Rho Irrel) a_Bullet)
  | Pattern_CApp : forall a1, Pattern a1 -> Pattern (a_CApp a1 g_Triv).

Hint Constructors Pattern.


Inductive Pattern_like_tm : tm -> Prop :=
  | Pat_tm_Fam : forall F, Pattern_like_tm (a_Fam F)
  | Pat_tm_AppR : forall a1 nu a2, Pattern_like_tm a1 -> lc_tm a2 ->
                                  Pattern_like_tm (a_App a1 nu a2)
  | Pat_tm_CApp : forall a1, Pattern_like_tm a1 ->
                             Pattern_like_tm (a_CApp a1 g_Triv).

Hint Constructors Pattern_like_tm.

Fixpoint tms_Pattern_like_tm (a : tm) := match a with
   | a_Fam F => []
   | a_App a1 (Role _) a' => tms_Pattern_like_tm a1 ++ [ a' ]
   | a_App a1 (Rho Irrel) a_Bullet => tms_Pattern_like_tm a1
   | a_CApp a1 g_Triv => tms_Pattern_like_tm a1
   | _ => []
   end.

Definition uniq_atoms_pattern p := NoDup (vars_Pattern p).

Fixpoint head_const (a : tm) : tm := match a with
  | a_Fam F => a_Fam F
  | a_App a' nu b => head_const a'
  | a_CApp a' g_Triv => head_const a'
  | _ => a_Bullet
  end.

(*
Lemma RolePath_head : forall a Rs, RolePath a Rs -> head_const a = a_Fam F.
Proof. intros. induction H; eauto.
Qed. *)

Fixpoint pat_app_roles (a : tm) : list role := match a with
  | a_Fam F => []
  | a_App a1 (Role R) (a_Var_f _) => pat_app_roles a1 ++ [ R ]
  | a_App a1 (Rho Irrel) a_Bullet => pat_app_roles a1
  | a_CApp a1 g_Triv => pat_app_roles a1
  | _ => []
  end.

Lemma combine_app : forall p l1 l2,
      combine (vars_Pattern p ++ l1) (pat_app_roles p ++ l2) =
      combine (vars_Pattern p) (pat_app_roles p) ++ combine l1 l2.
Proof. intros. generalize dependent l1. generalize dependent l2.
       induction p; intros; simpl; auto.
       - destruct nu.
         + destruct p2; auto. rewrite <- app_assoc.
           rewrite <- app_assoc. erewrite IHp1. simpl. erewrite IHp1.
           simpl. rewrite <- app_assoc. auto.
         + destruct rho. auto. destruct p2; auto.
       - destruct g; auto.
Qed.

Lemma pat_ctx_rctx : forall W G D F A p B, PatternContexts W G D F A p B ->
                     W = rev (combine (vars_Pattern p) (pat_app_roles p)).
Proof. intros. induction H; simpl; eauto.
       rewrite combine_app. rewrite rev_app_distr. simpl. f_equal. auto.
Qed.


(** free variables **)

Lemma Rename_fv_new_pattern : forall p b p' b' D D', Rename p b p' b' D D' ->
      AtomSetImpl.Subset (fv_tm_tm_tm p') D'.
Proof. intros. induction H; simpl in *; fsetdec.
Qed.

Lemma vars_pattern_fv : forall x p, In x (vars_Pattern p) ->
                                       x `in` fv_tm_tm_tm p.
Proof. intros. induction p; simpl in *; try contradiction.
       destruct nu. destruct p2; simpl in *; try contradiction.
       apply in_app_or in H. inversion H. apply AtomSetImpl.union_2. eauto.
       apply AtomSetImpl.union_3. apply in_inv in H0. inversion H0.
       subst. eauto. simpl in H1. contradiction.
       destruct rho. simpl in H; contradiction.
       destruct p2; simpl in *; try contradiction.
       apply AtomSetImpl.union_2. eauto.
       destruct g; simpl in *; try contradiction.
       apply AtomSetImpl.union_2. eauto.
Qed.

Lemma dom_combine_vars : forall p x,
      x `in` dom (combine (vars_Pattern p) (pat_app_roles p)) <->
      In x (vars_Pattern p).
Proof. intros. induction p; split; intros; simpl in *; try fsetdec.
        - destruct nu. destruct p2; simpl in *; try fsetdec.
          rewrite combine_app in H. apply dom_app in H. simpl in H.
          apply union_iff in H. apply in_or_app. inversion H. left.
          eapply IHp1; auto. right. econstructor. clear - H0. fsetdec.
          destruct rho. simpl in *; fsetdec.
          destruct p2; simpl in *; try fsetdec. eapply IHp1; auto.
        - destruct nu. destruct p2; simpl in *; try fsetdec.
          rewrite combine_app. apply dom_app. simpl.
          apply union_iff. apply in_app_or in H. inversion H. left.
          eapply IHp1; auto. right. clear - H0. inversion H0. subst. fsetdec.
          inversion H.
          destruct rho. simpl in *; fsetdec.
          destruct p2; simpl in *; try fsetdec. eapply IHp1; auto.
        - destruct g; simpl in *; try fsetdec. eapply IHp; auto.
        - destruct g; simpl in *; try fsetdec. eapply IHp; auto.
Qed.


Lemma dom_combine_fv : forall p x,
      x `in` dom (combine (vars_Pattern p) (pat_app_roles p)) ->
      x `in` fv_tm_tm_tm p.
Proof. intros. apply vars_pattern_fv. apply dom_combine_vars; auto.
Qed.

Lemma new_pattern_fv : forall p b p' b' D D' x,
      Rename p b p' b' D D' ->
      x `in` dom (combine (vars_Pattern p') (pat_app_roles p')) ->
      x `in` D'.
Proof. intros. apply dom_combine_fv in H0.
       eapply AtomSetProperties.in_subset. eauto. eapply Rename_fv_new_pattern.
       eauto.
Qed.

(** -------------------------------------------------------------- **)

(** Uniqueness **)

Lemma pat_ctx_vars_Pattern : forall W G D F A p B, PatternContexts W G D F A p B ->
            vars_Pattern p = rev (List.map fst W).
Proof. intros. induction H; eauto. simpl. rewrite IHPatternContexts.
       unfold one. auto.
Qed.

Lemma uniq_atoms_toplevel : forall F p b A R Rs,
      binds F (Ax p b A R Rs) toplevel -> uniq_atoms_pattern p.
Proof. intros. apply toplevel_inversion in H.
       inversion H as [W [G [D [B [H1 [_ [H3 _]]]]]]].
       apply pat_ctx_vars_Pattern in H1.
       apply rctx_uniq in H3. apply uniq_NoDup in H3.
       apply NoDup_reverse in H3. rewrite <- H1 in H3. auto.
Qed.


Lemma uniq_atoms_new_pattern : forall p p' b b' D D', Rename p b p' b' D D' ->
      uniq_atoms_pattern p'.
Proof. intros. induction H; unfold uniq_atoms_pattern in *; simpl; eauto.
       apply NoDup_nil. apply NoDup_add. rewrite app_nil_r. intro.
       apply H0. apply vars_pattern_fv in H1.
       move: (Rename_fv_new_pattern H) => h.
       apply AtomSetImpl.union_3. fsetdec. rewrite app_nil_r. auto.
Qed.


Lemma uniq_atoms_pattern_combine : forall p, uniq_atoms_pattern p <->
      uniq (combine (vars_Pattern p) (pat_app_roles p)).
Proof. intros.
       induction p; split; intros; unfold uniq_atoms_pattern in *; simpl in *;
       eauto; try apply NoDup_nil.
        - destruct nu. destruct p2; simpl; eauto.
          rewrite combine_app. apply NoDup_remove in H.
          rewrite app_nil_r in H. inversion H. apply uniq_reorder_1. simpl.
          econstructor. eapply IHp1. auto. intro. apply H1.
          apply dom_combine_vars. auto. destruct rho. simpl; eauto.
          destruct p2; simpl in *; eauto. simpl in *. eapply IHp1. auto.
        - destruct nu. destruct p2; try apply NoDup_nil.
          rewrite combine_app in H. apply uniq_reorder_1 in H.
          simpl in H. inversion H; subst. apply NoDup_add. rewrite app_nil_r.
          intro. apply H4. apply dom_combine_vars. auto. rewrite app_nil_r.
          apply IHp1. auto.
          destruct rho. apply NoDup_nil.
          destruct p2; try apply NoDup_nil. eapply IHp1. auto.
        - destruct g; simpl; eauto. apply IHp. auto.
        - destruct g; simpl; try apply NoDup_nil. apply IHp. auto.
Qed.

Lemma uniq_new_pattern_ctx : forall p b p' b' D D',
      Rename p b p' b' D D' ->
      uniq (combine (vars_Pattern p') (pat_app_roles p')).
Proof. intros. apply uniq_atoms_pattern_combine. eapply uniq_atoms_new_pattern;
       eauto.
Qed.


(** -------------------------------------------------------------- **)

Theorem roleing_Rename : forall b R p p' b' D D' W, Rename p b p' b' D D' ->
      AtomSetImpl.inter (fv_tm_tm_tm p \u dom W) (fv_tm_tm_tm p') [<=] empty ->
      roleing (W ++ rev (combine (vars_Pattern p) (pat_app_roles p))) b R ->
      roleing (W ++ rev (combine (vars_Pattern p') (pat_app_roles p'))) b' R.
Proof. intros. generalize dependent W.
       induction H; intros; simpl in *; eauto.
       - rewrite combine_app. rewrite rev_app_distr. simpl.
         rewrite combine_app in H2. rewrite rev_app_distr in H2.
         rewrite app_assoc in H2. simpl in H2.
         eapply subst_tm_roleing with (R1 := R0).
         + rewrite app_assoc.
           rewrite (cons_app_one _ (y,R0)).
           apply roleing_app_rctx.
           * move: (uniq_new_pattern_ctx H) => h. apply uniq_rev in h.
             move: (rctx_uniq H2) => h2. apply uniq_app_1 in h2.
             assert (dom (rev (combine (vars_Pattern p2) (pat_app_roles p2)))
                      [<=] fv_tm_tm_tm p2).
             { intro. intro. apply dom_rev in H3. rewrite rev_involutive in H3.
               apply dom_combine_fv in H3. auto. }
             apply uniq_app_4. auto. simpl. econstructor. auto.
             apply subset_notin with (S2 := fv_tm_tm_tm p2).
             apply subset_notin with (S2 := D'). clear - H0. fsetdec.
             eapply Rename_fv_new_pattern; eauto. auto.
             unfold disjoint. intro. intro. apply inter_iff in H4.
             inversion H4.
             assert (Q1 : a = x \/ a `in` dom W).
             { move: (AtomSetProperties.in_subset H5
                 (AtomSetProperties.subset_equal (dom_app _ _ _))) => q1.
               simpl in q1. apply union_iff in q1. clear - q1. fsetdec. 
             }
             assert (Q2 : a = y \/ a `in` fv_tm_tm_tm p2).
             { move: (AtomSetProperties.in_subset H6
                 (AtomSetProperties.subset_equal (dom_app _ _ _))) => q2.
               simpl in q2. apply union_iff in q2. clear - q2 H3. fsetdec. 
             }
             clear - H1 Q1 Q2.
             inversion Q1; inversion Q2; subst; clear Q1 Q2; fsetdec.
           * eapply IHRename; eauto. clear - H1. rewrite dom_app. simpl. fsetdec.
         + remember (rev (combine (vars_Pattern p2) (pat_app_roles p2))) as W'.
           replace ((y,R0) :: W') with ([(y,R0)] ++ W' ++ nil); eauto.
           apply roleing_app_rctx.
           simpl_env. econstructor. apply uniq_atoms_new_pattern in H.
           apply uniq_atoms_pattern_combine in H. rewrite HeqW'.
           apply uniq_rev. auto.
           intro. apply H0. apply AtomSetImpl.union_3.
           subst. apply dom_rev in H3. rewrite rev_involutive in H3.
           apply dom_combine_fv in H3.
           eapply AtomSetProperties.in_subset. eauto.
           eapply Rename_fv_new_pattern; eauto.
           simpl_env. eauto. rewrite app_nil_r. auto.
       - eapply IHRename; eauto. clear - H0. fsetdec.
       - eapply IHRename; eauto. clear - H0. fsetdec.
Qed.


Lemma ValuePath_head : forall a F, ValuePath a F -> head_const a = a_Fam F.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_head : forall F a R, CasePath R a F -> head_const a = a_Fam F.
Proof. intros. apply CasePath_ValuePath in H. apply ValuePath_head; auto.
Qed.

Lemma pattern_fv : forall p, Pattern p ->
                  (forall x, x `in` fv_tm_tm_tm p -> In x (vars_Pattern p)).
Proof. intros. induction H; simpl in *. fsetdec.
       apply AtomSetImpl.union_1 in H0. apply in_or_app. inversion H0.
       left. eauto. right. apply AtomSetImpl.singleton_1 in H1. subst.
       apply in_eq. eapply IHPattern. fsetdec. eapply IHPattern. fsetdec.
Qed.

Fixpoint matchsubst a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => b
  | (a_App a1 (Role R) a2, a_App p1 (Role R') (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Rho Irrel) a', a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => b
  end.


Lemma patctx_pattern : forall W G F D p B A, PatternContexts W G D F A p B ->
      Pattern p.
Proof. intros. induction H; eauto.
Qed.

Lemma patctx_pattern_head : forall W G F D p B A, PatternContexts W G D F A p B ->
      head_const p = a_Fam F.
Proof. intros. induction H; simpl; eauto.
Qed.

Lemma ValuePath_Pattern_like_tm : forall a F, ValuePath a F -> Pattern_like_tm a.
Proof. intros. induction H; eauto.
Qed.

Lemma axiom_pattern : forall F p b A R1 Rs,
      binds F (Ax p b A R1 Rs) toplevel -> Pattern p.
Proof. intros. assert (P : Sig toplevel). apply Sig_toplevel.
       induction P. inversion H. inversion H. inversion H2. eauto.
       inversion H. inversion H6; subst. eapply patctx_pattern; eauto.
       eauto.
Qed.

Lemma axiom_pattern_head : forall F p b A R1 Rs,
      binds F (Ax p b A R1 Rs) toplevel -> head_const p = a_Fam F.
Proof. intros. assert (P : Sig toplevel). apply Sig_toplevel.
       induction P. inversion H. inversion H. inversion H2. eauto.
       inversion H. inversion H6; subst. eapply patctx_pattern_head; eauto.
       eauto.
Qed.


Lemma matchsubst_ind_fun : forall a p b b',
      MatchSubst a p b b' -> matchsubst a p b = b'.
Proof. intros. induction H.
        - simpl. auto.
        - destruct R; simpl. rewrite IHMatchSubst. auto.
          rewrite IHMatchSubst. auto.
        - simpl. auto.
        - simpl. auto.
Qed.

Corollary MatchSubst_function : forall a p b b1 b2,
      MatchSubst a p b b1 -> MatchSubst a p b b2 -> b1 = b2.
Proof. intros. apply matchsubst_ind_fun in H.
       apply matchsubst_ind_fun in H0. rewrite H in H0. auto.
Qed.

Lemma tm_pattern_agree_tm : forall a p, tm_pattern_agree a p -> Pattern_like_tm a.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_pattern : forall a p, tm_pattern_agree a p -> Pattern p.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_refl : forall p, Pattern p -> tm_pattern_agree p p.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_sym : forall a p, Pattern a -> tm_pattern_agree a p ->
      tm_pattern_agree p a.
Proof. intros. generalize dependent p. induction H; intros.
       all: (inversion H0; subst; eauto).
Qed.

Lemma subtm_pattern_agree_pattern : forall a p, subtm_pattern_agree a p -> Pattern p.
Proof. intros. induction H; eauto. eapply tm_pattern_agree_pattern; eauto.
Qed.

Lemma subtm_pattern_agree_tm : forall a p, subtm_pattern_agree a p -> Pattern_like_tm a.
Proof. intros. induction H; eauto. eapply tm_pattern_agree_tm; eauto.
Qed.

Lemma tm_subpattern_agree_pattern : forall a p, tm_subpattern_agree a p -> Pattern p.
Proof. intros. induction H; eauto. eapply tm_pattern_agree_pattern; eauto.
Qed.

Lemma tm_subpattern_agree_tm : forall a p, tm_subpattern_agree a p -> Pattern_like_tm a.
Proof. intros. induction H; eauto. eapply tm_pattern_agree_tm; eauto.
Qed.

Lemma tm_pattern_agree_const_same : forall a p, tm_pattern_agree a p ->
         head_const a = head_const p.
Proof. intros. induction H; simpl; eauto.
Qed.

Lemma MatchSubst_match : forall a p b b', MatchSubst a p b b' ->
                                            tm_pattern_agree a p.
Proof. intros. induction H; eauto.
Qed.

Corollary MatchSubst_nexists : forall a p, ~(tm_pattern_agree a p) ->
                      forall b b', ~(MatchSubst a p b b').
Proof. intros. intro H'. apply MatchSubst_match in H'. contradiction.
Qed.

Lemma tm_pattern_agree_bullet_bullet : forall a p, tm_pattern_agree a p ->
                                       MatchSubst a p a_Bullet a_Bullet.
Proof. intros. induction H; eauto.
       assert (a_Bullet = tm_subst_tm_tm a2 x a_Bullet) by auto.
       assert (MatchSubst (a_App a1 (Role R) a2) (a_App p1 (Role R) (a_Var_f x))
       a_Bullet (tm_subst_tm_tm a2 x a_Bullet)). eauto. rewrite <- H1 in H2.
       auto.
Qed.

Lemma tm_pattern_agree_dec : forall a p, lc_tm a -> tm_pattern_agree a p \/
                                        ~(tm_pattern_agree a p).
Proof. intros. pose (P := match_dec p H). inversion P as [P1 | P2].
       left. eapply MatchSubst_match; eauto.
       right. intro. apply P2. eapply tm_pattern_agree_bullet_bullet; auto.
Qed.

Lemma tm_pattern_agree_app_contr : forall a p nu b, tm_pattern_agree a p ->
               tm_pattern_agree a (a_App p nu b) -> False.
Proof. intros a p nu b H. generalize dependent b.
       induction H; intros b H1; inversion H1; subst; eauto.
Qed.

Lemma tm_pattern_agree_capp_contr : forall a p, tm_pattern_agree a p ->
               tm_pattern_agree a (a_CApp p g_Triv) -> False.
Proof. intros a p H. induction H; intro H1; inversion H1; eauto.
Qed.

Corollary MatchSubst_app_nexists : forall a p b b',
          MatchSubst (a_App a (Rho Irrel) a_Bullet) p b b' ->
          ~(tm_pattern_agree a p).
Proof. intros. apply MatchSubst_match in H. intro. inversion H.
       subst. eapply tm_pattern_agree_app_contr; eauto.
Qed.

Corollary MatchSubst_capp_nexists : forall a p b b',
          MatchSubst (a_CApp a g_Triv) p b b' ->
          ~(tm_pattern_agree a p).
Proof. intros. apply MatchSubst_match in H. intro. inversion H.
       subst. eapply tm_pattern_agree_capp_contr; eauto.
Qed.

Lemma tm_pattern_agree_rename_inv_1 : forall a p p' b b' D D',
      tm_pattern_agree a p -> Rename p b p' b' D D' -> tm_pattern_agree a p'.
Proof. intros. generalize dependent p'. generalize dependent D.
       generalize dependent b'. generalize dependent D'.
       induction H; intros D' b' D p' H1; inversion H1; subst; eauto.
Qed.

Lemma tm_pattern_agree_rename_inv_2 : forall a p p' b b' D D',
      tm_pattern_agree a p -> Rename p' b' p b D D' -> tm_pattern_agree a p'.
Proof. intros. generalize dependent p'. generalize dependent D.
       generalize dependent b. generalize dependent D'.
       induction H; intros D' b D p' H1; inversion H1; subst; eauto.
Qed.

Inductive Pi_CPi_head_form : tm -> Prop :=
  | head_Pi : forall rho A B, Pi_CPi_head_form (a_Pi rho A B)
  | head_CPi : forall phi B, Pi_CPi_head_form (a_CPi phi B).
Hint Constructors Pi_CPi_head_form.

Inductive Abs_CAbs_head_form : tm -> Prop :=
  | head_Abs : forall rho a, Abs_CAbs_head_form (a_UAbs rho a)
  | head_CAbs : forall a, Abs_CAbs_head_form (a_UCAbs a).
Hint Constructors Abs_CAbs_head_form.

Inductive Const_App_CApp_head_form : tm -> Prop :=
   | head_Fam : forall F, Const_App_CApp_head_form (a_Fam F)
   | head_App : forall nu a b, Const_App_CApp_head_form (a_App a nu b)
  | head_CApp : forall a, Const_App_CApp_head_form (a_CApp a g_Triv).
Hint Constructors Const_App_CApp_head_form.

Lemma tm_pattern_agree_tm_const_app : forall a p, tm_pattern_agree a p ->
       Const_App_CApp_head_form a.
Proof. intros. induction H; eauto.
Qed.

Lemma subtm_pattern_agree_tm_const_app : forall a p, subtm_pattern_agree a p ->
       Const_App_CApp_head_form a.
Proof. intros. induction H; eauto. eapply tm_pattern_agree_tm_const_app; eauto.
Qed.

Lemma subtm_pattern_agree_dec : forall a p, lc_tm a -> subtm_pattern_agree a p \/
                                        ~(subtm_pattern_agree a p).
Proof. intros.
       induction a; try(right; intro P;
       apply subtm_pattern_agree_tm_const_app in P; inversion P; fail).
         - inversion H; subst. destruct (IHa1 H2) as [Q1 | Q2].
           left; eauto. pose (Q := tm_pattern_agree_dec p H).
           destruct Q as [Q3 | Q4]. left; eauto. right; intro.
           inversion H0; subst; contradiction.
         - destruct g; try (right; intro P;
           apply subtm_pattern_agree_tm_const_app in P; inversion P; fail).
           inversion H; subst. destruct (IHa H2) as [Q1 | Q2].
           left; eauto. pose (Q := tm_pattern_agree_dec p H).
           destruct Q as [Q3 | Q4]. left; eauto. right; intro.
           inversion H0; subst; contradiction.
         - pose (P := tm_pattern_agree_dec p H). destruct P as [P1 | P2].
           left; eauto. right; intro. inversion H0; subst; contradiction.
Qed.


(* If a agrees with p, then a can be substituted for p in b *)

Lemma MatchSubst_exists : forall a p, tm_pattern_agree a p -> forall b,
                          lc_tm b -> exists b', MatchSubst a p b b'.
Proof. intros a p H. induction H; intros.
        - exists b; auto.
        - pose (P := IHtm_pattern_agree b H1). inversion P as [b1 Q].
          exists (tm_subst_tm_tm a2 x b1). eauto.
        - pose (P := IHtm_pattern_agree b H1). inversion P as [b1 Q].
          exists b1; eauto.
        - pose (P := IHtm_pattern_agree b H0). inversion P as [b1 Q].
          exists b1; eauto.
Qed.

Lemma matchsubst_fun_ind : forall a p b b', tm_pattern_agree a p -> lc_tm b ->
      matchsubst a p b = b' -> MatchSubst a p b b'.
Proof. intros. generalize dependent b. generalize dependent b'.
       induction H; intros; eauto.
        - simpl in H1. rewrite <- H1. auto.
        - destruct R. simpl in H2. rewrite <- H2. eauto.
          simpl in H2. rewrite <- H2. eauto.
Qed.

Lemma Rename_tm_pattern_agree : forall p b p' b' D D', Rename p b p' b' D D' ->
      tm_pattern_agree p' p.
Proof. intros. induction H; eauto.
Qed.

Fixpoint rename p b D := match p with
   | a_Fam F => (p,b,empty)
   | a_App p1 (Role R) (a_Var_f x) => let (p'b',D') := rename p1 b D in
           let (p',b') := p'b' in
           let y := fresh(AtomSetImpl.elements (D \u D')) in
           (a_App p' (Role R) (a_Var_f y), tm_subst_tm_tm (a_Var_f y) x b',
           singleton y \u D')
   | a_App p1 (Rho Irrel) a_Bullet => let (p'b',D') := rename p1 b D in
           let (p',b') := p'b' in (a_App p' (Rho Irrel) a_Bullet,b',D')
   | a_CApp p1 g_Triv => let (p'b',D') := rename p1 b D in
           let (p',b') := p'b' in (a_CApp p' g_Triv,b',D')
   | _ => (p,b,D)
   end.

Lemma rename_Rename : forall p b D, Pattern p -> lc_tm b ->
      Rename p b (rename p b D).1.1 (rename p b D).1.2 D (rename p b D).2.
Proof. intros. generalize dependent b. generalize dependent D.
       induction H; intros.
        - simpl. eauto.
        - simpl. destruct (rename a1 b D) eqn:hyp. destruct p. simpl.
          econstructor. replace t0 with (rename a1 b D).1.1.
          replace t1 with (rename a1 b D).1.2.
          replace t with (rename a1 b D).2. eauto. rewrite hyp; auto.
          rewrite hyp; auto. rewrite hyp; auto.
          intro. apply AtomSetImpl.elements_1 in H1.
          assert (In (fresh (AtomSetImpl.elements (D \u t))) 
                     (AtomSetImpl.elements (D \u t))).
          rewrite <- InA_iff_In. auto. eapply fresh_not_in. eauto.
        - simpl. destruct (rename a1 b D) eqn:hyp. destruct p. simpl.
          econstructor. replace t0 with (rename a1 b D).1.1.
          replace t1 with (rename a1 b D).1.2.
          replace t with (rename a1 b D).2. eauto. rewrite hyp; auto.
          rewrite hyp; auto. rewrite hyp; auto.
        - simpl. destruct (rename a1 b D) eqn:hyp. destruct p. simpl.
          econstructor. replace t0 with (rename a1 b D).1.1.
          replace t1 with (rename a1 b D).1.2.
          replace t with (rename a1 b D).2. eauto. rewrite hyp; auto.
          rewrite hyp; auto. rewrite hyp; auto.
Qed.

Definition chain_substitution := fold_right (fun y => tm_subst_tm_tm (snd y) (fst y)).

Fixpoint tm_pattern_correspond (a p : tm) : list (atom * tm) := match (a,p) with
  | (a_Fam F, a_Fam F') => nil
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         (x, a2) :: tm_pattern_correspond a1 p1
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         (x, a2) :: tm_pattern_correspond a1 p1
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         tm_pattern_correspond a1 p1
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => tm_pattern_correspond a1 p1
  | (_,_) => nil
  end.

Lemma chain_sub_fam : forall l F,
                      chain_substitution (a_Fam F) l = a_Fam F.
Proof. intros. induction l. simpl; auto. destruct a; simpl. rewrite IHl.
       auto.
Qed.
(*
Lemma chain_sub_app : forall l nu a1 a2,
           chain_substitution l (a_App a1 nu a2) =
           a_App (chain_substitution l a1) nu (chain_substitution l a2).
Proof. intros. induction l. simpl; auto. destruct a; simpl. rewrite IHl.
       auto.
Qed.

Lemma chain_sub_var : forall l x, exists y, 
                      chain_substitution (map a_Var_f l) (a_Var_f x) = a_Var_f y.
Proof. intros. induction l. simpl. exists x; auto. destruct a.
       simpl. inversion IHl as [y P]. rewrite P. destruct (a == y).
       subst. exists t; simpl. destruct (y == y). auto. contradiction.
       exists y. simpl. destruct (y == a). symmetry in e. contradiction.
       auto.
Qed.

Lemma chain_sub_bullet : forall l, chain_substitution l a_Bullet = a_Bullet.
Proof. intros. induction l; try destruct a; simpl; try rewrite IHl; eauto.
Qed.

Lemma chain_sub_capp : forall l a, chain_substitution l (a_CApp a g_Triv) =
                       a_CApp (chain_substitution l a) g_Triv.
Proof. intros. induction l. simpl; auto. destruct a0; simpl. rewrite IHl; auto.
Qed.

Lemma RolePath_pat_rename_consist : forall a p l, RolePath_pat_consist a p ->
              RolePath_pat_consist a (chain_substitution (map a_Var_f l) p).
Proof. intros. induction H.
        - rewrite chain_sub_fam. eauto.
        - rewrite chain_sub_app. pose (P := chain_sub_var l x).
          inversion P as [y Q]. rewrite Q. eauto.
        - rewrite chain_sub_app. rewrite chain_sub_bullet. eauto.
        - rewrite chain_sub_capp; eauto.
Qed.


Lemma MatchSubst_permutation : forall a p b,
              chain_substitution (permutation a p) b = matchsubst a p b.
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto.
       all: try destruct g; try destruct nu; eauto.
       all: try destruct R; try destruct rho; eauto.
        - destruct p; eauto. destruct nu; eauto. destruct R; eauto.
          destruct p2; eauto. simpl. rewrite IHa1. auto.
        - destruct p; eauto. destruct nu; eauto. destruct R; eauto.
          destruct p2; eauto. simpl. rewrite IHa1. auto.
        - destruct a2; eauto. destruct p; eauto. destruct nu; eauto.
          destruct rho; eauto. destruct p2; eauto.
        - destruct p; eauto. destruct g; eauto.
        - destruct p; eauto.
Qed.

Inductive ICApp : tm -> tm -> Prop :=
   | ICApp_refl : forall a, ICApp a a
   | ICApp_IApp : forall a1 a2, ICApp a1 a2 -> ICApp a1 (a_App a2 (Rho Irrel) a_Bullet)
   | ICApp_CApp : forall a1 a2, ICApp a1 a2 -> ICApp a1 (a_CApp a2 g_Triv).

Lemma nonempty_perm : forall a p x l, x :: l = permutation a p ->
      exists a1 a2 p1 y, (ICApp (a_App a1 (Role Nom) a2) a /\ 
              ICApp (a_App p1 (Role Nom) (a_Var_f y)) p /\ x = (y, a2)
              /\ l = permutation a1 p1) \/
              (ICApp (a_App a1 (Role Rep) a2) a /\ 
              ICApp (a_App p1 (Role Rep) (a_Var_f y)) p /\ x = (y, a2)
              /\ l = permutation a1 p1).
Proof. intros a. induction a; intros p y l H; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       inversion H. exists a1, a2, p1, x. left; repeat split.
       eapply ICApp_refl. eapply ICApp_refl.
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       inversion H. exists a1, a2, p1, x. right; repeat split.
       eapply ICApp_refl. eapply ICApp_refl.
       destruct rho; try (inversion H; fail).
       destruct a2; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct rho; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       simpl in H. pose (P := IHa1 p1 y l ltac:(auto)).
       inversion P as [a2 [a3 [p2 [y0 [Q1 | Q2]]]]]. 
       exists a2, a3, p2, y0. inversion Q1 as [S1 [S2 [S3 S4]]].
       left; repeat split.
       eapply ICApp_IApp; auto.
       eapply ICApp_IApp; auto. auto. auto.
       exists a2, a3, p2, y0. inversion Q2 as [T1 [T2 [T3 T4]]]. 
       right; repeat split.
       eapply ICApp_IApp; auto.
       eapply ICApp_IApp; auto. auto. auto.
       destruct g; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct g; try (inversion H; fail).
       simpl in H. pose (P := IHa p y l ltac:(auto)).
       inversion P as [a2 [a3 [p2 [y0 [Q1 | Q2]]]]]. 
       exists a2, a3, p2, y0. inversion Q1 as [S1 [S2 [S3 S4]]].
       left; repeat split.
       eapply ICApp_CApp; auto.
       eapply ICApp_CApp; auto. auto. auto.
       exists a2, a3, p2, y0. inversion Q2 as [T1 [T2 [T3 T4]]]. 
       right; repeat split.
       eapply ICApp_CApp; auto.
       eapply ICApp_CApp; auto. auto. auto.
       destruct p; try (inversion H; fail).
Qed.

Lemma fv_ICApp : forall a1 a2 x, ICApp a1 a2 -> x `in` fv_tm_tm_tm a1 <->
                  x `in` fv_tm_tm_tm a2.
Proof. intros. generalize dependent x.
       induction H; intro.
         - split; auto.
         - pose (P := IHICApp x). inversion P as [P1 P2].
           split; intro; simpl in *; fsetdec.
         - pose (P := IHICApp x). inversion P as [P1 P2].
           split; intro; simpl in *; fsetdec.
Qed.

Lemma fv_perm_1 : forall a p l x a', l = permutation a p -> In (x,a') l ->
                    x `in` fv_tm_tm_tm p.
Proof. intros. generalize dependent a. generalize dependent p.
       dependent induction l; intros. inversion H0.
       inversion H0. subst. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [y [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp x) in S2. inversion S3; subst. simpl in S2.
       fsetdec. inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp x) in T2. inversion T3; subst. simpl in T2.
       fsetdec. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [y [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp x) in S2. apply S2. simpl. apply union_iff.
       left. eapply IHl; eauto.
       inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp x) in T2. apply T2. simpl. apply union_iff.
       left. eapply IHl; eauto.
Qed.

Lemma fv_perm_2 : forall a p l x a', l = permutation a p -> In (x,a') l ->
                  forall y, y `in` fv_tm_tm_tm a' -> y `in` fv_tm_tm_tm a.
Proof. intros. generalize dependent a. generalize dependent p.
       dependent induction l; intros. inversion H0.
       inversion H0. subst. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [z [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp y) in S1. inversion S3; subst. simpl in S1.
       fsetdec. inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp y) in T1. inversion T3; subst. simpl in T1.
       fsetdec. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [z [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp y) in S1. apply S1. simpl. apply union_iff.
       left. eapply IHl; eauto.
       inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp y) in T1. apply T1. simpl. apply union_iff.
       left. eapply IHl; eauto.
Qed.

Fixpoint rang (L : list (atom * tm)) : atoms :=
   match L with
   | nil => empty
   | (x, a) :: l => fv_tm_tm_tm a \u rang l
   end.

Lemma dom_Perm : forall A (L : list (atom * A)) L', Permutation L L' ->
                                                        dom L [=] dom L'.
Proof. intros. induction H; eauto. fsetdec. destruct x; simpl. fsetdec.
       destruct x, y. simpl. fsetdec. eapply transitivity; eauto.
Qed.

Lemma rang_Perm : forall L L', Permutation L L' -> rang L [=] rang L'.
Proof. intros. induction H; eauto. fsetdec. destruct x; simpl. fsetdec.
       destruct x, y. simpl. fsetdec. eapply transitivity; eauto.
Qed.

Lemma uniq_Perm : forall A (L : list (atom * A)) L', Permutation L L' ->
                                                      uniq L -> uniq L'.
Proof. intros. induction H; eauto. destruct x. apply uniq_cons_iff in H0.
       inversion H0. eapply uniq_cons_3; eauto. apply dom_Perm in H. fsetdec.
       destruct x, y. solve_uniq.
Qed.

Lemma Chain_sub_Permutation : forall L L' b,
        uniq L -> (forall x, x `in` dom L -> x `notin` rang L) ->
        Permutation L L' -> chain_substitution L b = chain_substitution L' b.
Proof. intros.
       dependent induction H1; intros.
         - auto.
         - simpl. destruct x. erewrite IHPermutation; eauto 1.
           solve_uniq. intros. simpl in H0. pose (P := H0 x ltac:(auto)).
           fsetdec.
         - destruct x, y. simpl. rewrite tm_subst_tm_tm_tm_subst_tm_tm.
           rewrite (tm_subst_tm_tm_fresh_eq t). auto. simpl in H0.
           pose (P := H0 a0 ltac:(auto)). fsetdec. simpl in H0.
           pose (P := H0 a ltac:(auto)). fsetdec.
           solve_uniq.
         - apply transitivity with (y := chain_substitution l' b).
           eapply IHPermutation1; eauto. eapply IHPermutation2.
           eapply uniq_Perm; eauto. pose (P := H1_). pose (Q := H1_).
           apply dom_Perm in P. apply rang_Perm in Q. intros.
           pose (S := H0 x). fsetdec.
Qed.

Lemma perm_pat_subst : forall a p x y a' l l1 l2, l = permutation a p ->
      uniq l -> y `notin` dom l -> l = l1 ++ (x, a') :: l2 ->
      permutation a (tm_subst_tm_tm (a_Var_f y) x p) = l1 ++ (y, a') :: l2.
Proof. intros. generalize dependent a. generalize dependent p.
       generalize dependent l1. generalize dependent l2.
       dependent induction l; intros. destruct l1; inversion H2.
       destruct l1; simpl in *. inversion H2; subst.
       apply nonempty_perm in H. inversion H as [a1 [a2 [p1 [z [P1 | P2]]]]].
       inversion P1 as [Q1 [Q2 [Q3 Q4]]]. inversion Q3; subst.
       solve_uniq. fsetdec.

Lemma chain_sub_subst : forall a p b x y,
    uniq (permutation a p) -> (forall z, z `in` p -> z `notin` fv_tm_tm_tm a) ->
    x `in` fv_tm_tm_tm p -> y `notin` fv_tm_tm_tm a ->
    chain_substitution (permutation a (tm_subst_tm_tm (a_Var_f y) x p))
    tm_subst_tm_tm (a_Var_f y) x b) = chain_substitution (permutation a p) b.
Proof. intros. rewrite MatchSubst_permutation. rewrite MatchSubst_permutation.

Lemma rename_chain_sub : forall a l p b,
 chain_substitution (permutation a (chain_substitution (map a_Var_f l) p))
 (chain_substitution (map a_Var_f l) b) = chain_substitution (permutation a p) b.
Proof. intros. generalize dependent p; generalize dependent b.
       induction l; intros. simpl. auto.
       destruct a0. rewrite map_cons.
       rewrite (Chain_sub_Permutation (L := [(a0, a_Var_f t)] ++ map a_Var_f l)
       (L' := map a_Var_f l ++ ([(a0, a_Var_f t)]))).
       rewrite chain_sub_append.
       rewrite (Chain_sub_Permutation (L := [(a0, a_Var_f t)] ++ map a_Var_f l)
       (L' := map a_Var_f l ++ ([(a0, a_Var_f t)]))).
       rewrite chain_sub_append. simpl. rewrite IHl.

Definition Nice a p := RolePath_pat_consist a p /\
              (forall x, x `in` fv_tm_tm_tm p -> x `notin` fv_tm_tm_tm a) /\
               uniq (permutation a p).

Fixpoint matchsubst2 a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => if F == F' then b else a_Bullet
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => a_Bullet
  end.

Lemma matchsubst_subst : forall a p b x y, x `notin` fv_tm_tm_tm a ->
      y `notin` fv_tm_tm_tm a -> matchsubst2 a p b =
    matchsubst2 a (tm_subst_tm_tm (a_Var_f y) x p) (tm_subst_tm_tm (a_Var_f y) x b).
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto.
         - destruct nu; eauto. destruct R; eauto.
           destruct p; eauto. simpl. destruct (x0 == x); auto.
           destruct nu; eauto. destruct R; eauto. destruct p2; eauto.
           simpl. destruct (x0 == x); auto.

Fixpoint matchsubst2 a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => if F == F' then b else a_Bullet
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         matchsubst2 a1 p1 (tm_subst_tm_tm a2 x b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         matchsubst2 a1 p1 (tm_subst_tm_tm a2 x b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => a_Bullet
  end.

Lemma matchsubst_matchsubst2 : forall a p b,
      (forall x, x `in` fv_tm_tm_tm a -> x `notin` fv_tm_tm_tm p) ->
       matchsubst a p b = matchsubst2 a p b.
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto. destruct p; eauto.
       destruct p2; eauto. destruct nu; eauto.
       destruct nu0; eauto. destruct R, R0; eauto; simpl.

*)


Lemma tm_subpattern_agree_const_same : forall a p, tm_subpattern_agree a p ->
 head_const a = head_const p.
Proof. intros. induction H; simpl; eauto.
       apply tm_pattern_agree_const_same; auto.
Qed.

Fixpoint pattern_length (a : tm) : nat := match a with
   a_Fam F => 0
 | a_App a nu b => pattern_length a + 1
 | a_CApp a g_Triv => pattern_length a + 1
 | _ => 0
 end.

Lemma tm_pattern_agree_length_same : forall a p, tm_pattern_agree a p ->
      pattern_length a = pattern_length p.
Proof. intros. induction H; simpl; eauto.
Qed.

Lemma tm_subpattern_agree_length_leq : forall a p, tm_subpattern_agree a p ->
      pattern_length a <= pattern_length p.
Proof. intros. induction H; simpl; try omega.
       eapply tm_pattern_agree_length_same in H; omega.
Qed.

Lemma subtm_pattern_agree_length_geq : forall a p, subtm_pattern_agree a p ->
      pattern_length a >= pattern_length p.
Proof. intros. induction H; simpl; try omega.
       eapply tm_pattern_agree_length_same in H; omega.
Qed.

Lemma tm_subpattern_agree_abs_cabs_contr : forall a p,
      tm_subpattern_agree a p -> Abs_CAbs_head_form a -> False.
Proof. intros. dependent induction H; eauto. inversion H0; subst; inversion H.
Qed.

Lemma tm_subpattern_agree_pi_cpi_contr : forall a p,
      tm_subpattern_agree a p -> Pi_CPi_head_form a -> False.
Proof. intros. dependent induction H; eauto. inversion H0; subst; inversion H.
Qed.

Lemma tm_subpattern_agree_case_contr : forall R a F apps b1 b2 p,
                tm_subpattern_agree (a_Pattern R a F apps b1 b2) p -> False.
Proof. intros. dependent induction H; eauto. inversion H.
Qed.

Lemma tm_subpattern_agree_app_contr : forall nu a b p, tm_pattern_agree a p ->
                  tm_subpattern_agree (a_App a nu b) p -> False.
Proof. intros. apply tm_pattern_agree_length_same in H.
       apply tm_subpattern_agree_length_leq in H0. simpl in H0. omega.
Qed.

Lemma tm_subpattern_agree_capp_contr : forall a p, tm_pattern_agree a p ->
                  tm_subpattern_agree (a_CApp a g_Triv) p -> False.
Proof. intros. apply tm_pattern_agree_length_same in H.
       apply tm_subpattern_agree_length_leq in H0. simpl in H0. omega.
Qed.

Lemma subtm_pattern_agree_app_contr : forall nu a b p,
      tm_pattern_agree (a_App a nu b) p -> subtm_pattern_agree a p -> False.
Proof. intros. apply tm_pattern_agree_length_same in H.
       apply subtm_pattern_agree_length_geq in H0. simpl in H. omega.
Qed.

Lemma subtm_pattern_agree_capp_contr : forall a p,
    tm_pattern_agree (a_CApp a g_Triv) p -> subtm_pattern_agree a p -> False.
Proof. intros. apply tm_pattern_agree_length_same in H.
       apply subtm_pattern_agree_length_geq in H0. simpl in H. omega.
Qed.

Lemma tm_subpattern_agree_sub_app : forall a nu b p,
              tm_subpattern_agree (a_App a nu b) p ->
              tm_subpattern_agree a p.
Proof. intros. dependent induction H; eauto. inversion H; subst. eauto.
       eauto.
Qed.

Lemma tm_subpattern_agree_sub_capp : forall a p,
              tm_subpattern_agree (a_CApp a g_Triv) p ->
              tm_subpattern_agree a p.
Proof. intros. dependent induction H; eauto. inversion H; subst. eauto.
Qed.

Lemma tm_subpattern_agree_rel_contr : forall a b p, tm_subpattern_agree
      (a_App a (Rho Rel) b) p -> False.
Proof. intros. dependent induction H; eauto. inversion H.
Qed.


(*
Lemma tm_subpattern_agree_irrel_bullet : forall a b p, tm_subpattern_agree
      (a_App a (Rho Irrel) b) p -> b = a_Bullet.
Proof. intros. dependent induction H; eauto. inversion H. auto.
Qed. *)

Ltac pattern_head := match goal with
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _ _,
          P3 : MatchSubst ?a ?p' _ _ |- _ ] =>
            pose (Q := tm_pattern_agree_rename_inv_2 (MatchSubst_match P3) P2);
            pose (Q1 := tm_pattern_agree_const_same Q);
            pose (Q2 := axiom_pattern_head P1);
            assert (U : head_const a = a_Fam F);
           [ rewrite Q1; rewrite Q2; auto |
             simpl in U; clear Q2; clear Q1; clear Q ]
       end.

Ltac pattern_head_tm_agree := match goal with
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : tm_pattern_agree ?a ?p |- _ ] =>
          pose (Q := axiom_pattern_head P1);
          pose (Q1 := tm_pattern_agree_const_same P2);
          assert (U1 : head_const a = a_Fam F);
          [ rewrite Q1; auto | clear Q1; clear Q ]
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : tm_subpattern_agree ?a ?p |- _ ] =>
          pose (Q := axiom_pattern_head P1);
          pose (Q1 := tm_subpattern_agree_const_same P2);
          assert (U1 : head_const a = a_Fam F);
          [ rewrite Q1; auto | clear Q1; clear Q ]
      end.

Ltac axioms_head_same := match goal with
     | [ P11 : binds ?F (Cs ?A1 ?Rs1) toplevel,
         P12 : binds ?F (Cs ?A2 ?Rs2) toplevel |- _ ] =>
         assert (P13 : Cs A1 Rs1 = Cs A2 Rs2);
         [ eapply binds_unique; eauto using uniq_toplevel 
         | inversion P13; subst; clear P13; clear P12]
     | [ P11 : binds ?F (Ax ?p1 ?b1 ?A1 ?R1 ?Rs1) toplevel,
         P12 : binds ?F (Cs ?A2 ?Rs2) toplevel |- _ ] =>
         assert (P13 : Ax p1 b1 A1 R1 Rs1 = Cs A2 Rs2);
         [ eapply binds_unique; eauto using uniq_toplevel | inversion P13]
     | [ P11 : binds ?F (Ax ?p1 ?b1 ?A1 ?R1 ?Rs1) toplevel,
         P12 : binds ?F (Ax ?p2 ?b2 ?A2 ?R2 ?Rs2) toplevel |- _ ] =>
         assert (P13 : Ax p1 b1 A1 R1 Rs1 = Ax p2 b2 A2 R2 Rs2);
         [ eapply binds_unique; eauto using uniq_toplevel |
                            inversion P13; subst; clear P13]
     end.

Inductive tm_tm_agree : tm -> tm -> Prop :=
  | tm_tm_agree_const : forall F, tm_tm_agree (a_Fam F) (a_Fam F)
  | tm_tm_agree_app_relR : forall a1 a2 nu b1 b2, tm_tm_agree a1 a2 -> lc_tm b1 ->
       lc_tm b2 -> tm_tm_agree (a_App a1 nu b1) (a_App a2 nu b2)
  | tm_tm_agree_capp : forall a1 a2, tm_tm_agree a1 a2 ->
                      tm_tm_agree (a_CApp a1 g_Triv) (a_CApp a2 g_Triv).
Hint Constructors tm_tm_agree.


Lemma tm_tm_agree_sym : forall a1 a2, tm_tm_agree a1 a2 -> tm_tm_agree a2 a1.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_tm_agree_trans : forall a1 a2 a3, tm_tm_agree a1 a2 ->
      tm_tm_agree a2 a3 -> tm_tm_agree a1 a3.
Proof. intros. generalize dependent a3. induction H; intros; eauto.
       inversion H2; subst. eauto. inversion H0; subst; eauto.
Qed.

Lemma tm_pattern_agree_tm_tm_agree : forall a p, tm_pattern_agree a p ->
      tm_tm_agree a p.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_cong : forall a1 a2 p, tm_pattern_agree a1 p ->
              tm_tm_agree a1 a2 -> tm_pattern_agree a2 p.
Proof. intros. generalize dependent p. induction H0; intros; eauto.
         - destruct nu. inversion H2; subst. eauto.
           destruct rho. inversion H2. inversion H2; subst. eauto.
         - inversion H; subst. eauto.
Qed.

Lemma subtm_pattern_agree_cong : forall a1 a2 p, subtm_pattern_agree a1 p ->
              tm_tm_agree a1 a2 -> subtm_pattern_agree a2 p.
Proof. intros. generalize dependent a2. induction H; intros; eauto.
        - econstructor. eapply tm_pattern_agree_cong; eauto.
        - destruct nu. inversion H1; subst. eauto.
          destruct rho. inversion H1; subst; eauto.
          inversion H1; subst; eauto.
        - inversion H0; subst. eauto.
Qed.

Lemma tm_subpattern_agree_cong : forall a1 a2 p, tm_subpattern_agree a1 p ->
              tm_tm_agree a1 a2 -> tm_subpattern_agree a2 p.
Proof. intros. generalize dependent a2. induction H; intros; eauto.
       econstructor. eapply tm_pattern_agree_cong; eauto.
Qed.

Lemma tm_tm_agree_refl : forall a, Pattern_like_tm a -> tm_tm_agree a a.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_tm_agree_head_same : forall a1 a2, tm_tm_agree a1 a2 ->
      head_const a1 = head_const a2.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_tm_agree_resp_ValuePath : forall a a' F,
      ValuePath a F -> tm_tm_agree a a' -> ValuePath a' F.
Proof. intros. generalize dependent a'.
       induction H; intros a' H1; inversion H1; subst; eauto.
Qed.

Lemma tm_pattern_agree_ValuePath : forall a p, tm_pattern_agree a p ->
      forall F b p' A R Rs, binds F (Ax p' b A R Rs) toplevel ->
      tm_subpattern_agree p p' -> ValuePath a F.
Proof. intros a p H. induction H; intros.
       - apply tm_subpattern_agree_const_same in H0.
         move: (axiom_pattern_head H) => h. rewrite <- H0 in h.
         simpl in H. inversion h; subst. eauto.
       - econstructor. auto. eapply IHtm_pattern_agree. eauto.
         eapply tm_subpattern_agree_sub_app. eauto.
       - econstructor. auto. eapply IHtm_pattern_agree. eauto.
         eapply tm_subpattern_agree_sub_app. eauto.
       - econstructor. eapply IHtm_pattern_agree. eauto.
         eapply tm_subpattern_agree_sub_capp. eauto.
Qed.

Lemma axiom_ValuePath : forall F p b A R Rs,
      binds F (Ax p b A R Rs) toplevel -> ValuePath p F.
Proof. intros. move: (axiom_pattern H) => h.
       eapply tm_pattern_agree_ValuePath; eauto.
       eapply tm_pattern_agree_refl. auto. econstructor.
       eapply tm_pattern_agree_refl. auto.
Qed.

(* TODO: why do we have both MultiPar (ett.ott) and multipar *)
Inductive multipar W ( a : tm) : tm -> role -> Prop :=
| mp_refl : forall R, roleing W a R -> multipar W a a R
| mp_step : forall R b c, Par W a b R -> multipar W b c R ->
                                             multipar W a c R.

Hint Constructors multipar.

Lemma pattern_like_tm_par : forall a a1 W R F p b A R1 Rs, 
      Par W a a1 R -> binds F (Ax p b A R1 Rs) toplevel ->
      tm_subpattern_agree a p -> ~(tm_pattern_agree a p) ->
      (Abs_CAbs_head_form a1 -> False) /\ tm_tm_agree a a1.
Proof. intros. generalize dependent p. induction H; intros; eauto.
         - split. intro. eapply tm_subpattern_agree_abs_cabs_contr; eauto.
           apply tm_tm_agree_refl. eapply tm_subpattern_agree_tm; eauto.
         - assert False. eapply IHPar1; eauto.
           eapply tm_subpattern_agree_sub_app; eauto.
           intro. eapply tm_subpattern_agree_app_contr; eauto.
           contradiction.
         - split. intro. inversion H4. econstructor. eapply IHPar1; eauto.
           eapply tm_subpattern_agree_sub_app; eauto.
           intro. eapply tm_subpattern_agree_app_contr; eauto.
           eapply Par_lc1; eauto. eapply Par_lc2; eauto.
         - assert False. eapply IHPar; eauto.
           eapply tm_subpattern_agree_sub_capp; eauto.
           intro. eapply tm_subpattern_agree_capp_contr; eauto. contradiction.
         - split. intro. inversion H3. econstructor. eapply IHPar. eauto.
           eapply tm_subpattern_agree_sub_capp; eauto.
           intro. eapply tm_subpattern_agree_capp_contr; eauto.
         - assert False.
           eapply tm_subpattern_agree_abs_cabs_contr; eauto.
           contradiction.
         - assert False. eapply tm_subpattern_agree_pi_cpi_contr; eauto.
           contradiction.
         - assert False.
           eapply tm_subpattern_agree_abs_cabs_contr; eauto. contradiction.
         - assert False. eapply tm_subpattern_agree_pi_cpi_contr; eauto.
           contradiction.
         - pattern_head_tm_agree. simpl in U1.
           inversion U1; subst. 
           axioms_head_same. inversion H3; subst.
           contradiction.
         - pattern_head. pattern_head_tm_agree. simpl in U1.
           assert (P : tm_tm_agree a a').
             { eapply IHPar1; eauto.
               eapply tm_subpattern_agree_sub_app; eauto. intro.
               eapply tm_subpattern_agree_app_contr; eauto.
             }
           assert (F = F0).
             { apply tm_tm_agree_head_same in P.
               rewrite U in P. rewrite U1 in P. inversion P; auto.
             }
           subst. axioms_head_same.
           pose (P1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H4) H3).
           assert False. apply H8. eapply tm_pattern_agree_cong. apply P1.
           econstructor. apply tm_tm_agree_sym; auto.
           eapply Par_lc2; eauto. eapply Par_lc1; eauto. contradiction.
         - pattern_head. pattern_head_tm_agree. simpl in U1.
           assert (P : tm_tm_agree a a').
             { eapply IHPar; eauto.
               eapply tm_subpattern_agree_sub_capp; eauto. intro.
               eapply tm_subpattern_agree_capp_contr; eauto.
             }
           assert (F = F0).
             { apply tm_tm_agree_head_same in P.
               rewrite U in P. rewrite U1 in P. inversion P; auto.
             }
           subst. axioms_head_same.
           pose (P1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H3) H2).
           assert False. apply H7. eapply tm_pattern_agree_cong. apply P1.
           econstructor. apply tm_tm_agree_sym; auto. contradiction.
         - split. intro. inversion H5.
           apply tm_subpattern_agree_case_contr in H3. contradiction.
         - split. intro. inversion H8.
           apply tm_subpattern_agree_case_contr in H6. contradiction.
         - assert False.
           eapply tm_subpattern_agree_case_contr; eauto. contradiction.
Qed.

Fixpoint applyArgs (a : tm) (b : tm) : tm := match a with
   | a_Fam F => b
   | a_App a' (Role _) b' => a_App (applyArgs a' b) (Rho Rel) b'
   | a_App a' (Rho Rel) b' => a_App (applyArgs a' b) (Rho Rel) b'
   | a_App a' (Rho Irrel) b' => a_App (applyArgs a' b) (Rho Irrel) b'
   | a_CApp a' g_Triv => a_CApp (applyArgs a' b) g_Triv
   | _ => a_Bullet
   end.


Lemma ApplyArgs_applyArgs : forall a b b', ApplyArgs a b b' ->
                             applyArgs a b = b'.
Proof. intros. induction H; simpl; subst; eauto.
       destruct rho; auto.
Qed.

Lemma applyArgs_ApplyArgs : forall R a F b b', CasePath R a F -> lc_tm b ->
                          applyArgs a b = b' -> ApplyArgs a b b'.
Proof. intros. generalize dependent b'. apply CasePath_ValuePath in H.
       induction H; intros; simpl in *; subst; eauto.
       destruct nu; try destruct rho; eauto.
Qed.

Ltac pattern_head_same := match goal with
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _ _,
          P3 : MatchSubst ?a ?p' _ _,
          P4 : binds ?F' (Ax _ _ _ _ _) toplevel,
          P5 : CasePath _ ?a' ?F' |- _ ] => pattern_head;
            pose (Q := CasePath_head P5); simpl in Q;
            assert (U1 : a_Fam F = a_Fam F');
            [ eapply transitivity; symmetry; eauto |
                 inversion U1; subst; clear U1; clear Q; axioms_head_same ]
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _ _,
          P3 : MatchSubst ?a ?p' _ _,
          P4 : binds ?F' (Ax _ _ _ _ _) toplevel,
          P5 : ValuePath ?a' ?F' |- _ ] => pattern_head;
            pose (Q := ValuePath_head P5); simpl in Q;
            assert (U1 : a_Fam F = a_Fam F');
            [ eapply transitivity; symmetry; eauto |
                 inversion U1; subst; clear U1; clear Q; axioms_head_same ]
       | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _ _,
          P3 : MatchSubst ?a ?p' _ _,
          P4 : binds ?F' (Cs _ _) toplevel,
          P5 : ValuePath ?a' ?F' |- _ ] => pattern_head;
            pose (Q := ValuePath_head P5); simpl in Q;
            assert (U1 : a_Fam F = a_Fam F');
            [ eapply transitivity; symmetry; eauto |
                 inversion U1; subst; clear U1; clear Q; axioms_head_same ]
       end.

Lemma uniq_CasePath : forall F1 F2 a R, CasePath R a F1 -> CasePath R a F2 ->
                       F1 = F2.
Proof. intros. apply CasePath_head in H. apply CasePath_head in H0.
       rewrite H0 in H. inversion H. auto.
Qed.

Lemma ValuePath_cs_par_ValuePath : forall a F A Rs W a' R, ValuePath a F ->
                 binds F (Cs A Rs) toplevel -> Par W a a' R ->
                 ValuePath a' F /\ tm_tm_agree a a'.
Proof. intros. generalize dependent a'. induction H; intros; eauto.
        - inversion H1; subst; eauto. axioms_head_same.
          axioms_head_same.
        - axioms_head_same.
        - inversion H2; subst. split; auto.
          apply tm_tm_agree_refl. eapply ValuePath_Pattern_like_tm; eauto.
          assert (ValuePath (a_UAbs rho a'0) F).
          apply IHValuePath; auto. subst. inversion H3.
          split; econstructor. eapply Par_lc2; eauto. eapply IHValuePath; eauto.
          eapply IHValuePath; eauto. eapply Par_lc1; eauto.
          eapply Par_lc2; eauto.
          assert (head_const a = head_const a'0).
          { inversion H7. apply tm_tm_agree_head_same.
            eapply pattern_like_tm_par; eauto. }
            pattern_head_same. eapply transitivity. symmetry; eauto.
            auto.
        - inversion H1; subst. split; auto.
          apply tm_tm_agree_refl. eapply ValuePath_Pattern_like_tm; eauto.
          assert (ValuePath (a_UCAbs a'0) F).
          eapply IHValuePath; eauto. inversion H2.
          split; econstructor. eapply IHValuePath; eauto.
          eapply IHValuePath; eauto.
          pattern_head_same. eapply transitivity.
          symmetry; eauto. inversion H4. apply tm_tm_agree_head_same.
          eapply pattern_like_tm_par; eauto.
Qed.

Lemma ValuePath_ax_par_ValuePath_1 : forall a F p b A R1 Rs W a' R,
      ValuePath a F -> binds F (Ax p b A R1 Rs) toplevel ->
      ~(SubRole R1 R) -> Par W a a' R -> ValuePath a' F /\  ~(SubRole R1 R)
       /\ tm_tm_agree a a'.
Proof. intros. generalize dependent a'. generalize dependent p.
       induction H; intros; eauto.
         - axioms_head_same.
         - axioms_head_same. inversion H2; subst.
           split; eauto. axioms_head_same.
           contradiction.
         - inversion H3; subst. 
           + split; eauto. split; auto.
             apply tm_tm_agree_refl. eapply ValuePath_Pattern_like_tm; eauto.
           + assert (ValuePath (a_UAbs rho a'0) F).
             eapply IHValuePath; eauto. inversion H4.
           + pose (P := IHValuePath p H2 a'0 H10). inversion P.
             inversion H5. split; eauto. econstructor.
             eapply Par_lc2; eauto. auto. split; auto. econstructor; auto.
             eapply Par_lc2; eauto.
           + pattern_head_same. eapply transitivity. symmetry; eauto.
             inversion H8. apply tm_tm_agree_head_same.
             eapply pattern_like_tm_par; eauto. contradiction.
          - inversion H2; subst.
           + split; eauto. split; auto.
             apply tm_tm_agree_refl. eapply ValuePath_Pattern_like_tm; eauto.
           + assert (ValuePath (a_UCAbs a'0) F).
             eapply IHValuePath; eauto. inversion H3.
           + pose (P := IHValuePath p H0 a'0 H5).
             inversion P. inversion H4. split; auto.
           + pattern_head_same. eapply transitivity.
             symmetry; eauto. inversion H5. apply tm_tm_agree_head_same.
             eapply pattern_like_tm_par; eauto. contradiction.
Qed.


Lemma tm_subpattern_agree_base : forall F p, Pattern p ->
      head_const p = a_Fam F -> tm_subpattern_agree (a_Fam F) p.
Proof. intros. induction H; eauto. simpl in H0. inversion H0; eauto.
Qed.

Lemma ValuePath_ax_par_ValuePath_2 : forall a F p b A R1 Rs W a' R,
      ValuePath a F -> binds F (Ax p b A R1 Rs) toplevel ->
      ~(subtm_pattern_agree a p) -> Par W a a' R -> ValuePath a' F /\
      ~(subtm_pattern_agree a' p) /\ tm_tm_agree a a'.
Proof. intros. generalize dependent a'. generalize dependent p.
       induction H; intros; eauto.
         - axioms_head_same.
         - inversion H2; subst. eauto.
           axioms_head_same. assert False. apply H1. eauto. contradiction.
         - inversion H3; subst.
           + repeat split; simpl in *; eauto. eapply tm_tm_agree_refl; eauto.
             econstructor. eapply ValuePath_Pattern_like_tm; eauto. auto.
           + assert (ValuePath (a_UAbs rho a'0) F).
             eapply IHValuePath; eauto. inversion H4.
           + pose (P := IHValuePath p H1 ltac:(eauto) a'0 H10).
             inversion P as [P1 [P2 P3]].
             split; eauto. econstructor. eapply Par_lc2; eauto. auto.
             assert (Q : tm_tm_agree (a_App a'0 nu b'0) (a_App a nu b')).
             { apply tm_tm_agree_sym in P3. apply Par_lc2 in H11. eauto. }
             split. intro. apply H2. eapply subtm_pattern_agree_cong; eauto.
             apply tm_tm_agree_sym; auto.
           + inversion H8.
             assert (tm_tm_agree a a'0). eapply pattern_like_tm_par; eauto.
             pose (X1 := tm_tm_agree_head_same H6). pattern_head_same.
             eapply transitivity. symmetry; eauto. auto.
             pose (Q1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H15) H12).
             assert False. eapply H2. econstructor.
             eapply tm_pattern_agree_cong. eapply Q1. econstructor.
             eapply tm_tm_agree_sym; eauto. eapply Par_lc2; eauto. auto.
             contradiction.
          - inversion H2; subst.
           + repeat split; simpl in *; eauto. eapply tm_tm_agree_refl; eauto.
             eapply ValuePath_Pattern_like_tm; eauto.
           + assert (ValuePath (a_UCAbs a'0) F).
             eapply IHValuePath; eauto. inversion H3.
           + pose (P := IHValuePath p H0 ltac:(eauto) a'0 H5).
             inversion P as [P1 [P2 P3]].
             repeat split. econstructor. eapply IHValuePath; eauto. intro.
             apply H1. pose (Q := tm_tm_agree_sym P3).
             eapply subtm_pattern_agree_cong; eauto. eauto.
           + inversion H5.
             assert (tm_tm_agree a a'0). eapply pattern_like_tm_par; eauto.
             pose (X1 := tm_tm_agree_head_same H11). pattern_head_same.
             eapply transitivity. symmetry; eauto. auto.
             pose (Q1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H8) H7).
             assert False. eapply H1. econstructor.
             eapply tm_pattern_agree_cong. eapply Q1. econstructor.
             eapply tm_tm_agree_sym; eauto. auto. contradiction.
Qed.

Lemma Par_CasePath_agree : forall F a R W a', CasePath R a F -> Par W a a' R ->
                                        CasePath R a' F /\ tm_tm_agree a a'.
Proof. intros. generalize dependent a'. induction H; intros.
       - pose (P := ValuePath_cs_par_ValuePath H H0 H1). inversion P.
         eauto.
       - pose (P := ValuePath_ax_par_ValuePath_1 H H0 H1 H2).
         inversion P. inversion H4. eauto.
       - pose (P := ValuePath_ax_par_ValuePath_2 H H0 H1 H2).
         inversion P as [P1 [P2 P3]]. eauto.
Qed.

Lemma Par_CasePath : forall F a R W a', CasePath R a F -> Par W a a' R ->
                                        CasePath R a' F.
Proof. intros. eapply Par_CasePath_agree; eauto.
Qed.

Lemma AppsPath_head : forall R a F n, AppsPath R a F n -> head_const a = a_Fam F.
Proof. intros. induction H; eauto.
Qed.

Lemma AppsPath_ValuePath : forall R a F n, AppsPath R a F n -> ValuePath a F.
Proof. intros. induction H; eauto.
Qed.

Lemma Par_AppsPath : forall F a W a' n n',
     AppsPath Nom a F n /\ SatApp F n' ->
     Par W a a' Nom -> AppsPath Nom a' F n /\ SatApp F n'.
Proof. intros. generalize dependent a'. inversion H.
       dependent induction H0; intros.
       - inversion H2; subst. split; eauto. axioms_head_same.
       - inversion H3; subst. split; eauto. axioms_head_same. contradiction.
       - inversion H3; subst. split; eauto. split.
         econstructor. eapply Par_lc2; eauto. eapply IHAppsPath.
         split; eauto. all:auto. inversion H8; subst.
         apply AppsPath_head in H1. inversion H2; subst. pattern_head_tm_agree.
         rewrite H1 in U1. inversion U1; subst.
         axioms_head_same. pattern_head_tm_agree. rewrite H1 in U1.
         inversion U1; subst. axioms_head_same. contradiction.
       - inversion H3; subst. split; eauto.
         assert (AppsPath Nom (a_UAbs Irrel a'0) F Apps5). eapply IHAppsPath.
         split; auto. all: auto. inversion H4. split.
         econstructor. eapply Par_lc2; eauto. eapply IHAppsPath.
         split; auto. all:auto. inversion H8; subst.
         apply AppsPath_head in H1. inversion H2; subst. pattern_head_tm_agree.
         rewrite H1 in U1. inversion U1; subst.
         axioms_head_same. pattern_head_tm_agree. rewrite H1 in U1.
         inversion U1; subst. axioms_head_same. contradiction.
       - inversion H2; subst. split; eauto.
         assert (AppsPath Nom (a_UCAbs a'0) F Apps5). eapply IHAppsPath.
         split; auto. all: auto. inversion H3. split.
         econstructor. eapply IHAppsPath.
         split; auto. all:auto. inversion H5; subst.
         apply AppsPath_head in H0. inversion H1; subst. pattern_head_tm_agree.
         rewrite H0 in U1. inversion U1; subst.
         axioms_head_same. pattern_head_tm_agree. rewrite H0 in U1.
         inversion U1; subst. axioms_head_same. contradiction.
Qed.


Ltac invert_par :=
     try match goal with
      | [ Hx : CasePath _ _ _,
          Hy : Par _ _ _ _ |- _ ] => apply CasePath_ValuePath in Hx;
               inversion Hy; subst;
                    match goal with
                 | [ Hz : MatchSubst _ _ _ _,
                     Hw : Rename _ _ _ _ _ |- _ ] =>
                       pose (Q := tm_pattern_agree_rename_inv_2
                              (MatchSubst_match Hz) Hw); inversion Q
                 | [ Hu : ValuePath _ _ |- _ ] => inversion Hu
                     end; fail
      | [ Hx : AppsPath _ _ _ _ ,
          Hy : Par _ _ _ _ |- _ ] =>
               apply AppsPath_ValuePath in Hx;
               inversion Hy; subst;
                    match goal with
                 | [ Hz : MatchSubst _ _ _ _,
                     Hw : Rename _ _ _ _ _ |- _ ] =>
                       pose (Q := tm_pattern_agree_rename_inv_2
                              (MatchSubst_match Hz) Hw); inversion Q
                 | [ Hu : ValuePath _ _ |- _ ] => inversion Hu
                     end; fail
           end.

Lemma CasePath_Par : forall F a R W a', Value R a' -> CasePath R a F -> Par W a' a R -> CasePath R a' F.
Proof. intros. induction H; invert_par.
       pose (P := Par_CasePath H H1). apply CasePath_head in P.
       apply CasePath_head in H0. rewrite P in H0. inversion H0; subst; auto.
Qed.


Lemma tm_tm_agree_AppsPath : forall R a F n a', AppsPath R a F n ->
      tm_tm_agree a a' -> AppsPath R a' F n.
Proof. intros. generalize dependent a'.
       induction H; intros; eauto.
       all: try (inversion H0; subst; eauto; fail).
       all: try (inversion H1; subst; eauto).
Qed.

Lemma AppsPath_Par : forall F a W a' n, Value Nom a' ->
                     AppsPath Nom a F n ->
                     Par W a' a Nom -> AppsPath Nom a' F n.
Proof. intros. dependent induction H; invert_par.
       move: (Par_CasePath_agree H H1) => h. inversion h.
       eapply tm_tm_agree_AppsPath. eauto. apply tm_tm_agree_sym.
       auto.
Qed.

Lemma Value_par_Value : forall R v W v', Value R v -> Par W v v' R -> Value R v'.
Proof. intros. generalize dependent W. generalize dependent v'.
       induction H; intros.
        - inversion H0; subst. auto.
        - inversion H1; subst. auto.
          apply Par_lc2 in H1. econstructor.
          inversion H1; auto. auto.
        - inversion H1; subst. auto.
          apply Par_lc2 in H1. econstructor.
          inversion H1; auto. auto.
        - inversion H1; subst. auto.
        - inversion H0; subst. auto.
          apply Par_lc2 in H0. econstructor. auto.
        - inversion H1; subst. eauto. eapply Value_UAbsIrrel with (L := L \u L0).
          intros. eapply H0. auto. eapply H7; eauto.
        - inversion H1; subst. auto.
        - inversion H0; subst. auto. econstructor.
          eapply Par_lc2; eauto.
        - pose (P := Par_CasePath H H0). eauto.
Qed.

Lemma multipar_CasePath :  forall F a R W a', CasePath R a F ->
                       multipar W a a' R -> CasePath R a' F.
Proof. intros. induction H0; auto. apply IHmultipar. eapply Par_CasePath; eauto.
Qed.

Lemma multipar_CasePath_join_head : forall F1 F2 W a1 a2 c R,
      multipar W a1 c R -> multipar W a2 c R ->
      CasePath R a1 F1 -> CasePath R a2 F2 -> F1 = F2.
Proof. intros. eapply multipar_CasePath in H; eauto.
       eapply multipar_CasePath in H0; eauto. eapply uniq_CasePath; eauto.
Qed.
(*
Lemma app_roleing_nom : forall W a rho b R, roleing W (a_App a (Rho rho) b) R ->
                               roleing W b Nom.
Proof. intros. dependent induction H; eauto. eapply role_a_Bullet.
       eapply rctx_uniq; eauto.
Qed.
*)
Lemma CasePath_ax_par_contr : forall R a F F' p b A R1 Rs p' b' D D' a',
       CasePath R a F -> binds F' (Ax p b A R1 Rs) toplevel ->
       Rename p b p' b' D D' -> MatchSubst a p' b' a' -> SubRole R1 R -> False.
Proof. intros. pattern_head.
       pose (Q := CasePath_head H).
       assert (a_Fam F = a_Fam F'). eapply transitivity. symmetry. eauto. auto.
       inversion H4; subst.
       inversion H; subst.
         + axioms_head_same.
         + axioms_head_same. contradiction.
         + axioms_head_same.
           pose (Q1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H2) H1).
           apply H7; eauto.
Qed.

Lemma apply_args_par : forall a b c a' b' c' W R2 F, ApplyArgs a b c ->
                       CasePath Nom a F -> Par W a a' Nom -> Par W b b' R2 ->
                       ApplyArgs a' b' c' -> Par W c c' R2.
Proof. intros. generalize dependent a'. generalize dependent b'.
       generalize dependent c'.
       (* By induction on ApplyArgs *)
       induction H; intros.
         - inversion H1; subst. inversion H3; subst. auto.
           assert (F0 = F). { eapply CasePath_head in H0; simpl in H0; 
           inversion H0; auto. } subst.
           inversion H0; subst; axioms_head_same. contradiction. assert False.
           apply H9. eauto. contradiction.
         - (* First App case, nu is (Rho R) *)
           (* Have a path:  a R a'  that reduces to some a'0. *)
           inversion H3; subst.  (* case on how a R a' reduces.  *)
             + (* Headed by a constant, but not enough arguments. *)
               inversion H4; subst. econstructor.
               eapply IHApplyArgs; eauto. eapply CasePath_app; eauto.
               inversion H5; eauto. econstructor.
               simpl.
               inversion H5; eauto. subst.
               have e: param R Nom = Nom. unfold param, min. destruct R; auto.
               rewrite <- e. auto.
             + inversion H4; subst. econstructor.
               eapply IHApplyArgs; eauto. eapply CasePath_app; eauto.
               simpl in *.
               have e: param R Nom = Nom. unfold param, min. destruct R; auto.
               rewrite <- e. auto.
             + (* Axiom pattern match *)
               (* a R a' reduces by unfolding an Axiom 
                *)
               split_hyp. 
               assert (tm_tm_agree a a'1).
               { eapply pattern_like_tm_par; eauto. }

               move: (MatchSubst_match H16) => P.
               assert (tm_pattern_agree (a_App a (Role R) a') p').
               { eapply tm_pattern_agree_cong. eapply P.               
               econstructor. eapply tm_tm_agree_sym; eauto.
               eapply Par_lc2; eauto. eapply Par_lc1; eauto. }
               destruct (MatchSubst_exists H9 (MatchSubst_lc3 H16)) as [a0 Q]. 
               assert False. eapply CasePath_ax_par_contr; eauto. 
               contradiction. 
         - (* Second App case, nu is (Rho rho) *)
            inversion H3; subst.
             + inversion H4; subst. econstructor.
               eapply IHApplyArgs; eauto. eapply CasePath_app; eauto.
               inversion H5; eauto. econstructor.
               simpl.
               inversion H5; eauto. 
             + eapply CasePath_app in H0. 
               pose (P := Par_CasePath H0 H11).
               apply CasePath_ValuePath in P. 
               inversion P.
             + inversion H4; subst. econstructor. eapply IHApplyArgs; eauto.
               eapply CasePath_app; eauto. auto.
             + inversion H9. assert (tm_tm_agree a a'1).
               eapply pattern_like_tm_par; eauto.
               pose (P := MatchSubst_match H16).
               assert (tm_pattern_agree (a_App a (Rho rho) a') p').
               eapply tm_pattern_agree_cong. eapply P.
               econstructor. eapply tm_tm_agree_sym; eauto.
               eapply Par_lc2; eauto. eapply Par_lc1; eauto.
               destruct (MatchSubst_exists H12 (MatchSubst_lc3 H16)) as [a0 Q]. 
               assert False. eapply CasePath_ax_par_contr; eauto. 
               contradiction.
         - inversion H1; subst.
             + inversion H3; subst. econstructor.
               eapply IHApplyArgs; eauto. eapply CasePath_capp; eauto.
               inversion H4; eauto.
             + eapply CasePath_capp in H0. pose (P := Par_CasePath H0 H6).
               apply CasePath_ValuePath in P. inversion P.
             + inversion H3; subst. econstructor. eapply IHApplyArgs; eauto.
               eapply CasePath_capp; eauto.
             + inversion H6. assert (tm_tm_agree a a'0).
               eapply pattern_like_tm_par; eauto.
               pose (P := MatchSubst_match H9).
               assert (tm_pattern_agree (a_CApp a g_Triv) p').
               eapply tm_pattern_agree_cong. eapply P.
               econstructor. eapply tm_tm_agree_sym; eauto.
               destruct (MatchSubst_exists H13 (MatchSubst_lc3 H9)) as [a0 Q].
               assert False. eapply CasePath_ax_par_contr; eauto. contradiction. 
Qed.

Fixpoint tm_to_roles (a : tm) : roles := match a with
    | a_Fam F => nil
    | a_App a1 (Role R) _ => tm_to_roles a1 ++ [ R ]
    | a_App a1 (Rho Rel) _ => tm_to_roles a1 ++ [Nom]
    | a_App a1 (Rho Irrel) _ => tm_to_roles a1
    | a_CApp a1 _ => tm_to_roles a1
    | _ => nil
    end.


Lemma RolePath_inversion : forall a Rs, RolePath a Rs ->
         (exists F A,  binds F (Cs A (tm_to_roles a ++ Rs)) toplevel /\ head_const a = a_Fam F) \/
         (exists F p b A R, binds F (Ax p b A R (tm_to_roles a ++ Rs))  toplevel
                                /\ head_const a = a_Fam F).
Proof. intros. induction H; simpl; eauto.
        - right. exists F, p, a, A, R1; eauto.
        - inversion IHRolePath as [[F [A [H1 H2]]] | [F [p [a1 [A [R2 [H1 H2]]]]]]].
          left. exists F, A. rewrite <- app_assoc. eauto.
          right. exists F, p, a1, A, R2. rewrite <- app_assoc. eauto.
        - inversion IHRolePath as [[F [A [H1 H2]]] | [F [p [a1 [A [R2 [H1 H2]]]]]]].
          left. exists F, A. rewrite <- app_assoc. eauto.
          right. exists F, p, a1, A, R2. rewrite <- app_assoc. eauto.
Qed.

Lemma PatternContexts_roles : forall W G D p F B A, PatternContexts W G D F B p A ->
      tm_to_roles p = range W.
Proof. intros. induction H; simpl; eauto. rewrite IHPatternContexts; eauto.
Qed.

Lemma tm_pattern_agree_roles : forall a p, tm_pattern_agree a p ->
      tm_to_roles a = tm_to_roles p.
Proof. intros. induction H; simpl; eauto. f_equal; eauto.
Qed.

Lemma subtm_pattern_agree_roles : forall a p, subtm_pattern_agree a p ->
      exists Rs', tm_to_roles a = tm_to_roles p ++ Rs'.
Proof. intros. induction H; simpl; eauto.
       exists nil; rewrite app_nil_r; apply tm_pattern_agree_roles; auto.
       destruct nu; try destruct rho; eauto. 
       all: inversion IHsubtm_pattern_agree as [Rs' H1].
       all: eexists; erewrite H1; erewrite app_assoc; eauto.
Qed.

Lemma RolePath_subtm_pattern_agree_contr : forall a F p b A R Rs R0 Rs',
      RolePath a (R0 :: Rs') -> binds F (Ax p b A R Rs) toplevel -> head_const a = a_Fam F ->
      ~(subtm_pattern_agree a p).
Proof. intros. apply RolePath_inversion in H.
       inversion H as [[F0 [A1 [h1 h2]]] | [F0 [p1 [b1 [A1 [R1 [h1 h2]]]]]]].
       all: match goal with 
              [ H1 : head_const ?a = a_Fam ?F, H2 : head_const ?a = a_Fam ?F0 |- _] => 
              rewrite H1 in H2; inversion H2; clear H2; subst end.
        - axioms_head_same.
        - axioms_head_same. intro. apply toplevel_inversion in H0.
          inversion H0 as [W [G [D [B [H3 [H4 [H5 [H6 _]]]]]]]].
          apply PatternContexts_roles in H3. rewrite <- H6 in H3.
          apply subtm_pattern_agree_roles in H2.
          inversion H2 as [Rs'' H7]. rewrite H7 in H3.
          rewrite <- app_assoc in H3.
          rewrite <- app_nil_r with (l := tm_to_roles p1) in H3.
          rewrite <- app_assoc in H3. apply app_inv_head in H3.
          apply app_cons_not_nil in H3. auto.
Qed.

Lemma tm_subst_tm_tm_back_forth_mutual : forall x y,
      (forall b, y `notin` fv_tm_tm_tm b ->
      tm_subst_tm_tm (a_Var_f x) y (tm_subst_tm_tm (a_Var_f y) x b) = b) /\
      (forall brs, y `notin` fv_tm_tm_brs brs ->
      tm_subst_tm_brs (a_Var_f x) y (tm_subst_tm_brs (a_Var_f y) x brs) = brs) /\
      (forall g, y `notin` fv_tm_tm_co g ->
      tm_subst_tm_co (a_Var_f x) y (tm_subst_tm_co (a_Var_f y) x g) = g) /\
      (forall phi, y `notin` fv_tm_tm_constraint phi ->
      tm_subst_tm_constraint (a_Var_f x) y
          (tm_subst_tm_constraint (a_Var_f y) x phi) = phi).
Proof. intros. apply tm_brs_co_constraint_mutind; intros; simpl;
       try (simpl in H; try simpl in H1; try simpl in H2; f_equal; eauto; fail).
       destruct (eq_var x0 x). simpl. rewrite eq_dec_refl. subst. auto.
       simpl. destruct (eq_var x0 y). subst. simpl in H. fsetdec. auto.
Qed.

Lemma tm_subst_tm_tm_back_forth : forall x y b, y `notin` fv_tm_tm_tm b ->
      tm_subst_tm_tm (a_Var_f x) y (tm_subst_tm_tm (a_Var_f y) x b) = b.
Proof. eapply tm_subst_tm_tm_back_forth_mutual; eauto.
Qed.


Lemma MatchSubst_subst : forall a p x y b b',
   tm_pattern_agree a p -> lc_tm b -> x `notin` fv_tm_tm_tm p ->
   y `notin` (fv_tm_tm_tm a \u fv_tm_tm_tm p \u fv_tm_tm_tm b) ->
   MatchSubst a p (tm_subst_tm_tm (a_Var_f y) x b) b' ->
   MatchSubst a p b (tm_subst_tm_tm (a_Var_f x) y b').
Proof. intros. generalize dependent x. generalize dependent y.
       generalize dependent b. generalize dependent b'. induction H; intros.
         - inversion H3; subst. rewrite tm_subst_tm_tm_back_forth.
           fsetdec. eauto.
         - simpl in H2. simpl in H3. inversion H4; subst.
           rewrite tm_subst_tm_tm_tm_subst_tm_tm. simpl.
           fsetdec. fsetdec.
           rewrite (tm_subst_tm_tm_fresh_eq a2). fsetdec. eauto.
         - simpl in H2. simpl in H3. inversion H4; subst. eauto.
         - simpl in H2. simpl in H1. inversion H3; subst. eauto.
Qed.

Lemma MatchSubst_subst_tm : forall a p b b' e x,
     tm_pattern_agree a p -> lc_tm e ->
     AtomSetImpl.inter (singleton x \u fv_tm_tm_tm e)
          (fv_tm_tm_tm p \u fv_tm_tm_tm b) [<=] empty ->
     MatchSubst a p b b' ->
     MatchSubst (tm_subst_tm_tm e x a) p b (tm_subst_tm_tm e x b').
Proof. intros. generalize dependent b'.
       induction H; intros; simpl in *.
        - inversion H2; subst. rewrite tm_subst_tm_tm_fresh_eq.
          fsetdec. eauto.
        - inversion H3; subst. rewrite tm_subst_tm_tm_tm_subst_tm_tm.
          fsetdec. fsetdec. econstructor. apply tm_subst_tm_tm_lc_tm; auto.
          eapply IHtm_pattern_agree. fsetdec. auto.
        - inversion H3; subst. econstructor. apply tm_subst_tm_tm_lc_tm; auto.
          eapply IHtm_pattern_agree. fsetdec. auto.
        - inversion H2; subst. econstructor.
          eapply IHtm_pattern_agree. fsetdec. auto.
Qed.


Lemma MatchSubst_subst_co : forall a p b b' g c,
     tm_pattern_agree a p -> lc_co g ->
     AtomSetImpl.inter (singleton c \u fv_tm_tm_co g)
          (fv_tm_tm_tm p \u fv_co_co_tm b) [<=] empty ->
     MatchSubst a p b b' ->
     MatchSubst (co_subst_co_tm g c a) p b (co_subst_co_tm g c b').
Proof. intros. generalize dependent b'.
       induction H; intros; simpl in *.
        - inversion H2; subst. rewrite co_subst_co_tm_fresh_eq.
          fsetdec. eauto.
        - inversion H3; subst. rewrite co_subst_co_tm_tm_subst_tm_tm.
          fsetdec. econstructor. apply co_subst_co_tm_lc_tm; auto.
          eapply IHtm_pattern_agree. fsetdec. auto.
        - inversion H3; subst. econstructor. apply co_subst_co_tm_lc_tm; auto.
          eapply IHtm_pattern_agree. fsetdec. auto.
        - inversion H2; subst. econstructor.
          eapply IHtm_pattern_agree. fsetdec. auto.
Qed.

Lemma Subset_trans : forall D1 D2 D3, AtomSetImpl.Subset D1 D2 ->
      AtomSetImpl.Subset D2 D3 -> AtomSetImpl.Subset D1 D3.
Proof. intros. fsetdec.
Qed.

Lemma Subset_union : forall D1 D1' D2 D2', D1 [<=] D1' -> D2 [<=] D2' ->
         (D1 \u D2) [<=] (D1' \u D2').
Proof. intros. fsetdec.
Qed.

Lemma Superset_cont_sub : forall x S1 S2, S1 [<=] S2 -> x `in` S1 -> x `in` S2.
Proof. intros. fsetdec.
Qed.



Lemma Rename_fv_body : forall p b p' b' D D',
      Rename p b p' b' D D' ->
      AtomSetImpl.Subset (fv_tm_tm_tm b')
     ((AtomSetImpl.diff (fv_tm_tm_tm b) (fv_tm_tm_tm p)) \u fv_tm_tm_tm p').
Proof. intros. induction H; intros; simpl in *; auto.
         - pose (P := fv_tm_tm_tm_tm_subst_tm_tm_upper a2 (a_Var_f y) x).
           simpl in P.
           eapply Subset_trans. eauto. fsetdec.
         - fsetdec.
         - fsetdec.
Qed.

Lemma Rename_new_body_fv : forall p b p' b' D D',
      Rename p b p' b' D D' -> fv_tm_tm_tm b [<=] fv_tm_tm_tm p ->
      fv_tm_tm_tm b' [<=] D'.
Proof. intros. move: (Rename_fv_body H) => h. eapply Subset_trans. eauto.
       rewrite AtomSetProperties.diff_subset_equal.
       apply AtomSetProperties.union_subset_3. apply Subset_empty_any.
       eapply Rename_fv_new_pattern; eauto. auto.
Qed.

Lemma Rename_new_body_fv_co : forall p b p' b' D D',
      Rename p b p' b' D D' -> fv_co_co_tm b [<=] empty ->
      fv_co_co_tm b' [<=] empty.
Proof. intros. induction H; eauto.
       rewrite fv_co_co_tm_tm_subst_tm_tm_upper. simpl.
       apply AtomSetProperties.union_subset_3; eauto.
Qed.

Lemma Rename_inter_empty : forall p b p' b' D D', Rename p b p' b' D D' ->
      (forall x, x `in` D -> x `notin` D').
Proof. intros. generalize dependent x. induction H; intros; eauto.
       pose (P := IHRename x0 H1). fsetdec.
Qed.

Lemma MatchSubst_fv : forall a p b b', MatchSubst a p b b' ->
      AtomSetImpl.Subset (fv_tm_tm_tm b')
     ((AtomSetImpl.diff (fv_tm_tm_tm b) (fv_tm_tm_tm p)) \u fv_tm_tm_tm a).
Proof. intros. induction H; simpl. auto.
       pose (P := fv_tm_tm_tm_tm_subst_tm_tm_upper b2 a x).
       eapply Subset_trans. eauto. fsetdec. fsetdec. fsetdec.
Qed.

Lemma Rename_MatchSubst_fv : forall p b p' b' D D' a b'',
      Rename p b p' b' D D' -> MatchSubst a p' b' b'' ->
      AtomSetImpl.Subset (fv_tm_tm_tm b'')
      ((AtomSetImpl.diff (fv_tm_tm_tm b) (fv_tm_tm_tm p)) \u fv_tm_tm_tm a).
Proof. intros. apply Rename_fv_body in H. apply MatchSubst_fv in H0.
       fsetdec.
Qed.

Lemma ValuePath_dec : forall W a R, roleing W a R -> (exists F, ValuePath a F)
                                     \/ (forall F, ~(ValuePath a F)).
Proof. intros. induction H.
       all: try (right; intros F' h1; inversion h1; fail).
        - inversion IHroleing1. inversion H1 as [F h1].
          left; exists F. econstructor. eapply roleing_lc. eauto. auto.
          right. intros F h1. inversion h1; subst. apply (H1 F); auto.
        - inversion IHroleing1. inversion H1 as [F' h1].
          left; exists F'. econstructor. eapply roleing_lc. eauto. auto.
          right. intros F' h1. inversion h1; subst. apply (H1 F'); auto.
        - inversion IHroleing. inversion H0 as [F h1].
          left; exists F. eauto.
          right. intros F h1. inversion h1; subst. apply (H0 F); auto.
        - left. exists F; eauto.
        - left. exists F; eauto.
Qed.

Lemma ValuePath_const_form : forall a F, ValuePath a F ->
      (exists A Rs, binds F (Cs A Rs) toplevel) \/
      (exists p a A R1 Rs, binds F (Ax p a A R1 Rs) toplevel).
Proof. intros. induction H.
        - left. exists A, Rs. auto.
        - right. exists p, a, A, R1, Rs. auto.
        - inversion IHValuePath. left; eauto. right; eauto.
        - inversion IHValuePath. left; eauto. right; eauto.
Qed.
 
Lemma decide_CasePath : forall W a R, roleing W a R -> (exists F, CasePath R a F) \/
                                     (forall F, ~(CasePath R a F)).
Proof. intros. induction H.
  all: try (right; intros F' h1; apply CasePath_ValuePath in h1;
                                            inversion h1; fail).
  - inversion IHroleing1. inversion H1 as [F h1].
    move: (CasePath_ValuePath h1) => h2.
    move: (ValuePath_const_form h2) => h3.
    destruct h3 as [[A [Rs h4]] | [p [a' [A [R1 [Rs h4]]]]]].
    left. exists F; econstructor. econstructor. eapply roleing_lc; eauto.
    auto. eauto.
    move: (sub_dec R1 R) => h5. inversion h5.
    assert (U: lc_tm (a_App a (Rho rho) b)).
    econstructor; eapply roleing_lc; eauto.
    move: (subtm_pattern_agree_dec p U) => h5'. inversion h5; inversion h5'.
    right. intros F' h6.
    move: (CasePath_ValuePath h6) => h7. apply ValuePath_head in h7.
    simpl in h7. move: (ValuePath_head h2) => h8. rewrite h7 in h8.
    inversion h8; subst. inversion h6; subst. axioms_head_same.
    axioms_head_same. contradiction. axioms_head_same. contradiction.
    left. exists F. eapply CasePath_UnMatch; eauto. econstructor.
    eapply roleing_lc; eauto. auto. contradiction. contradiction.
    left. exists F. eapply CasePath_Const; eauto. econstructor.
    eapply roleing_lc; eauto. auto. right. intros F h1. 
    inversion h1; subst. inversion H2; subst. eapply H1; eauto.
    eapply H1; eapply CasePath_Const; eauto. inversion H2; subst. eauto.
    eapply H1; eapply CasePath_UnMatch; eauto. inversion H2; subst. eauto.
    intro. apply H4. eapply subtm_pattern_agree_App. eapply roleing_lc; eauto.
    auto.
  - inversion IHroleing1. inversion H1 as [F' h1].
    move: (CasePath_ValuePath h1) => h2.
    move: (ValuePath_const_form h2) => h3.
    destruct h3 as [[A [Rs' h4]] | [p [a' [A [R2 [Rs' h4]]]]]].
    left. exists F'; econstructor. econstructor. eapply roleing_lc; eauto.
    auto. eauto.
    move: (sub_dec R2 R) => h5. inversion h5.
    assert (U: lc_tm (a_App a (Role R1) b)).
    econstructor; eapply roleing_lc; eauto.
    move: (subtm_pattern_agree_dec p U) => h5'. inversion h5; inversion h5'.
    right. intros F'' h6.
    move: (CasePath_ValuePath h6) => h7. apply ValuePath_head in h7.
    simpl in h7. move: (ValuePath_head h2) => h8. rewrite h7 in h8.
    inversion h8; subst. inversion h6; subst. axioms_head_same.
    axioms_head_same. contradiction. axioms_head_same. contradiction.
    left. exists F'. eapply CasePath_UnMatch; eauto. econstructor.
    eapply roleing_lc; eauto. auto. contradiction. contradiction.
    left. exists F'. eapply CasePath_Const; eauto. econstructor.
    eapply roleing_lc; eauto. auto. right. intros F' h1. 
    inversion h1; subst. inversion H2; subst. eapply H1; eauto.
    eapply H1; eapply CasePath_Const; eauto. inversion H2; subst. eauto.
    eapply H1; eapply CasePath_UnMatch; eauto. inversion H2; subst. eauto.
    intro. apply H4. eapply subtm_pattern_agree_App. eapply roleing_lc; eauto.
    auto.
  - inversion IHroleing. inversion H0 as [F h1].
    move: (CasePath_ValuePath h1) => h2.
    move: (ValuePath_const_form h2) => h3.
    destruct h3 as [[A [Rs h4]] | [p [a' [A [R1 [Rs h4]]]]]].
    left. exists F; eauto.
    move: (sub_dec R1 R) => h5. inversion h5.
    assert (U: lc_tm (a_CApp a g_Triv)).
    econstructor. eapply roleing_lc; eauto. auto.
    move: (subtm_pattern_agree_dec p U) => h5'. inversion h5; inversion h5'.
    right. intros F' h6.
    move: (CasePath_ValuePath h6) => h7. apply ValuePath_head in h7.
    simpl in h7. move: (ValuePath_head h2) => h8. rewrite h7 in h8.
    inversion h8; subst. inversion h6; subst. axioms_head_same.
    axioms_head_same. contradiction. axioms_head_same. contradiction.
    left. exists F. eapply CasePath_UnMatch; eauto. contradiction.
    contradiction.
    left. exists F. eapply CasePath_Const; eauto. right. intros F h1. 
    inversion h1; subst. inversion H1; subst. eapply H0; eauto.
    eapply H0; eapply CasePath_Const; eauto. inversion H1; subst. eauto.
    eapply H0; eapply CasePath_UnMatch; eauto. inversion H1; subst. eauto.
  - left. exists F. eauto.
  - move: (sub_dec R R1) => h1. inversion h1.
    assert (U: lc_tm (a_Fam F)). eauto.
    move: (subtm_pattern_agree_dec p U) => h1'. inversion h1; inversion h1'.
    right. intros F' h2.
    move: (CasePath_ValuePath h2) => h3. apply ValuePath_head in h3.
    simpl in h3. inversion h3; subst. inversion h2; subst. axioms_head_same.
    axioms_head_same. contradiction. axioms_head_same. contradiction.
    left. exists F. eapply CasePath_UnMatch; eauto. contradiction.
    contradiction. left. exists F. eapply CasePath_Const; eauto.
Qed.

Lemma CasePath_dec : forall W a R F, roleing W a R -> 
                     CasePath R a F \/ ~(CasePath R a F).
Proof. intros. eapply decide_CasePath in H. inversion H.
       inversion H0 as [F' H1]. destruct (eq_dec F F'). subst. auto.
       right. intro. apply CasePath_head in H1. apply CasePath_head in H2.
       rewrite H2 in H1. inversion H1. contradiction. right. eauto.
Qed.


Lemma tm_pattern_agree_unsubst_tm : forall a b x p, Pattern_like_tm a ->
           tm_pattern_agree (tm_subst_tm_tm b x a) p -> tm_pattern_agree a p.
Proof. intros. generalize dependent p.
       induction H; intros; simpl in *; eauto.
       inversion H1; subst. eauto. eauto.
       inversion H0; subst. eauto.
Qed.

Lemma tm_pattern_agree_unsubst_co : forall a g c p, Pattern_like_tm a ->
           tm_pattern_agree (co_subst_co_tm g c a) p -> tm_pattern_agree a p.
Proof. intros. generalize dependent p.
       induction H; intros; simpl in *; eauto.
       inversion H1; subst. eauto. eauto.
       inversion H0; subst. eauto.
Qed.

Lemma subtm_pattern_agree_unsubst_tm : forall a b x p,  Pattern_like_tm a ->
      subtm_pattern_agree (tm_subst_tm_tm b x a) p -> subtm_pattern_agree a p.
Proof. intros. generalize dependent p. induction H; intros; simpl in *; eauto.
       inversion H1; subst. econstructor.
       eapply tm_pattern_agree_unsubst_tm; eauto.
       eapply subtm_pattern_agree_App; eauto.
       inversion H0; subst. econstructor.
       eapply tm_pattern_agree_unsubst_tm; eauto.
       eapply subtm_pattern_agree_CAppp; eauto.
Qed.

Lemma subtm_pattern_agree_unsubst_co : forall a g c p,  Pattern_like_tm a ->
      subtm_pattern_agree (co_subst_co_tm g c a) p -> subtm_pattern_agree a p.
Proof. intros. generalize dependent p. induction H; intros; simpl in *; eauto.
       inversion H1; subst. econstructor.
       eapply tm_pattern_agree_unsubst_co; eauto.
       eapply subtm_pattern_agree_App; eauto.
       inversion H0; subst. econstructor.
       eapply tm_pattern_agree_unsubst_co; eauto.
       eapply subtm_pattern_agree_CAppp; eauto.
Qed.

Lemma CasePath_subst_tm : forall F a b R x, CasePath R a F -> lc_tm b ->
                   CasePath R (tm_subst_tm_tm b x a) F.
Proof. intros. inversion H; subst. econstructor; eauto.
       apply ValuePath_subst; auto. eapply CasePath_Const; eauto.
       apply ValuePath_subst; auto. eapply CasePath_UnMatch; eauto.
       apply ValuePath_subst; auto. intro. eapply H3.
       eapply subtm_pattern_agree_unsubst_tm; eauto.
       eapply ValuePath_Pattern_like_tm. eauto.
Qed.

Lemma CasePath_subst_co : forall F a g R c, CasePath R a F -> lc_co g ->
                   CasePath R (co_subst_co_tm g c a) F.
Proof. intros. inversion H; subst. econstructor; eauto.
       apply ValuePath_subst_co; auto. eapply CasePath_Const; eauto.
       apply ValuePath_subst_co; auto. eapply CasePath_UnMatch; eauto.
       apply ValuePath_subst_co; auto. intro. eapply H3.
       eapply subtm_pattern_agree_unsubst_co; eauto.
       eapply ValuePath_Pattern_like_tm. eauto.
Qed.

Lemma ValuePath_unsubst_tm : forall F a b x, Pattern_like_tm a ->
      ValuePath (tm_subst_tm_tm b x a) F -> ValuePath a F.
Proof. intros. induction H; simpl in *; eauto.
       inversion H0; subst. eauto with lngen lc.
       inversion H0; subst. eauto with lngen lc.
Qed.

Lemma CasePath_unsubst_tm : forall F a b R x, Pattern_like_tm a -> lc_tm b ->
      CasePath R (tm_subst_tm_tm b x a) F -> CasePath R a F.
Proof. intros. inversion H1; subst. econstructor; eauto.
       eapply ValuePath_unsubst_tm; eauto. eapply CasePath_Const; eauto.
       eapply ValuePath_unsubst_tm; eauto. eapply CasePath_UnMatch; eauto.
       eapply ValuePath_unsubst_tm; eauto. intro. eapply H4.
       eapply subtm_pattern_agree_subst_tm; eauto.
Qed.

Lemma CasePath_Value_unsubst_tm : forall F a b x R, Value R a -> lc_tm b ->
      CasePath R (tm_subst_tm_tm b x a) F -> CasePath R a F.
Proof. intros. induction H; simpl in *;
         try (apply CasePath_ValuePath in H1; inversion H1; fail).
       eapply CasePath_unsubst_tm; eauto.
       apply CasePath_ValuePath in H. eapply ValuePath_Pattern_like_tm; eauto.
Qed.

Lemma AppsPath_unsubst_tm : forall  a, Pattern_like_tm a -> 
      forall F b x n R, lc_tm b ->
      AppsPath R (tm_subst_tm_tm b x a) F n -> AppsPath R a F n.
Proof. 
  induction 1; intros; simpl in *; eauto.
  inversion H2; subst; eauto.
  inversion H1; subst; eauto.
Qed.


Lemma AppsPath_Value_unsubst_tm : forall F a b x n R, Value R a -> lc_tm b ->
      AppsPath R (tm_subst_tm_tm b x a) F n -> AppsPath R a F n.
Proof. 
  intros.
  inversion H; subst; simpl in *; try solve [inversion H1].
  eapply AppsPath_unsubst_tm; 
    eauto using ValuePath_Pattern_like_tm,  CasePath_ValuePath.
Qed.

Lemma ValuePath_unsubst_co : forall F a g c, Pattern_like_tm a ->
      ValuePath (co_subst_co_tm g c a) F -> ValuePath a F.
Proof. intros. induction H; simpl in *; eauto.
       inversion H0; subst. eauto with lngen lc.
       inversion H0; subst. eauto with lngen lc.
Qed.

Lemma CasePath_unsubst_co : forall F a g R c, Pattern_like_tm a -> lc_co g ->
      CasePath R (co_subst_co_tm g c a) F -> CasePath R a F.
Proof. intros. inversion H1; subst. econstructor; eauto.
       eapply ValuePath_unsubst_co; eauto. eapply CasePath_Const; eauto.
       eapply ValuePath_unsubst_co; eauto. eapply CasePath_UnMatch; eauto.
       eapply ValuePath_unsubst_co; eauto. intro. eapply H4.
       eapply subtm_pattern_agree_subst_co; eauto.
Qed.

Lemma CasePath_Value_unsubst_co : forall F a g c R, Value R a -> lc_co g ->
      CasePath R (co_subst_co_tm g c a) F -> CasePath R a F.
Proof. intros. induction H; simpl in *;
         try (apply CasePath_ValuePath in H1; inversion H1; fail).
       eapply CasePath_unsubst_co; eauto.
       apply CasePath_ValuePath in H. eapply ValuePath_Pattern_like_tm; eauto.
Qed.


Lemma AppsPath_unsubst_co : forall  a, Pattern_like_tm a -> 
      forall F g x n R, lc_co g ->
      AppsPath R (co_subst_co_tm g x a) F n -> AppsPath R a F n.
Proof. 
  induction 1; intros; simpl in *; eauto.
  inversion H2; subst; eauto.
  inversion H1; subst; eauto.
Qed.


Lemma AppsPath_Value_unsubst_co : forall F a g c n R, Value R a -> lc_co g ->
      AppsPath R (co_subst_co_tm g c a) F n -> AppsPath R a F n.
Proof. 
 intros.
  inversion H; subst; simpl in *; try solve [inversion H1].
  eapply AppsPath_unsubst_co; 
    eauto using ValuePath_Pattern_like_tm,  CasePath_ValuePath.
Qed.


Lemma ApplyArgs_subst_tm : forall a b c e x, lc_tm e -> ApplyArgs a b c ->
  ApplyArgs (tm_subst_tm_tm e x a)(tm_subst_tm_tm e x b)(tm_subst_tm_tm e x c).
Proof. intros. induction H0; simpl; eauto.
       all: econstructor; auto; apply tm_subst_tm_tm_lc_tm; auto.
Qed.

Lemma ApplyArgs_subst_co : forall a b c g y, lc_co g -> ApplyArgs a b c ->
  ApplyArgs (co_subst_co_tm g y a)(co_subst_co_tm g y b)(co_subst_co_tm g y c).
Proof. intros. induction H0; simpl; eauto.
       all: econstructor; auto; apply co_subst_co_tm_lc_tm; auto.
Qed.

Lemma snoc_destruct : forall n, n = A_nil \/ exists a1 n1, n = A_snoc n1 a1.
Proof. induction n. left; auto.
       destruct IHn. subst; simpl.
       right. exists App5. exists A_nil. auto.
       right. move: H => [a1 [n1 eq]].
       exists a1. exists (A_cons App5 n1). simpl. rewrite eq. auto.
Qed.

Lemma not_snoc_nil : forall a n, (A_snoc a n = A_nil) -> False.
Proof. induction a; simpl; intros; discriminate.
Qed.

Lemma snoc_injective2 : forall a1 n1 a2 n2, 
    A_snoc a1 n1 = A_snoc a2 n2 -> n1 = n2.
Proof.
intro a1. induction a1; intros; simpl in *.
destruct a2. simpl in *. inversion H. auto.
simpl in *. inversion H. symmetry in H2. eapply not_snoc_nil in H2. contradiction.
destruct a2. simpl in *. inversion H.
eapply not_snoc_nil in H2. contradiction.
simpl in *.
inversion H.
eapply IHa1. eauto.
Qed.

Lemma snoc_injective1 : forall a1 n1 a2 n2, 
    A_snoc a1 n1 = A_snoc a2 n2 -> a1 = a2.
Proof.
intro a1. induction a1; intros; simpl in *.
destruct a2. simpl in *. inversion H. auto.
simpl in *. inversion H. symmetry in H2. eapply not_snoc_nil in H2. contradiction.
destruct a2. simpl in *. inversion H.
eapply not_snoc_nil in H2. contradiction.
simpl in *.
inversion H.
f_equal. eauto.
Qed.

Lemma decide_AppsPath : forall W a R, roleing W a R -> 
                                 (forall F Apps, (AppsPath R a F Apps) \/
                                            (~(AppsPath R a F Apps))).
Proof. 
  induction 1.
  all: try solve [intros; right; move=> h; inversion h].
  all: intros.
  all: try clear IHroleing2.
  all: try (destruct rho; try solve [right; move=> h; inversion h]).
  all: destruct (snoc_destruct Apps) as [|[n1 [a1 eq]]]; subst.
  all: try solve [right;  move=> h; inversion h; eauto using not_snoc_nil].
  (* Destruct the app at the top *)
  all: try destruct n1; try destruct nu; try destruct rho; 
       try destruct (role_dec R1 R0); subst.
  all: try solve [right;  move=> h; inversion h; subst;
    with (A_snoc _ _ = A_snoc _ _ ) do 
         ltac:(fun h => apply snoc_injective2 in h; inversion h; subst; auto)].

  all: try edestruct (IHroleing1 F a1);
    try solve [left; econstructor; eauto using roleing_lc].

  all: try edestruct (IHroleing F a1);
    try solve [left; econstructor; eauto using roleing_lc].

  all: try solve [right; move=> h; inversion h; subst;
    with (A_snoc _ _ = A_snoc _ _ ) do 
         ltac:(fun h => apply snoc_injective1 in h; inversion h) end;
    subst; auto].

  destruct (eq_dec F F0). subst.
  left. eauto.
  right. move=> h; inversion h; subst; contradiction.

  destruct (eq_dec F F0). subst.
  destruct (sub_dec R R1).
  right. move=> h; inversion h; subst. 
  axioms_head_same.
  axioms_head_same.
  contradiction.
  left. eauto.
  right. move=> h; inversion h; subst; contradiction.
Qed.


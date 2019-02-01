Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Import FcEtt.toplevel.
Require Import FcEtt.ett_roleing.
Require Import FcEtt.ext_wf.

Lemma RolePath_ValuePath : forall a F Rs, RolePath a F Rs -> ValuePath a F.
Proof. intros. induction H; eauto.
Qed.


Lemma CasePath_ValuePath : forall R a F, CasePath R a F -> ValuePath a F.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_app : forall R a nu a' F, CasePath R (a_App a nu a') F ->
                            CasePath R a F.
Proof. intros. dependent induction H; inversion H; subst; eauto.
Qed.

Lemma CasePath_capp : forall R a F, CasePath R (a_CApp a g_Triv) F ->
                            CasePath R a F.
Proof. intros. dependent induction H; inversion H; subst; eauto.
Qed.

Lemma ValuePath_lc : forall F a, ValuePath a F -> lc_tm a.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_lc : forall F a R, CasePath R a F -> lc_tm a.
Proof. intros. apply CasePath_ValuePath in H. eapply ValuePath_lc; eauto.
Qed.

Lemma ValuePath_subst : forall F a b x, ValuePath a F -> lc_tm b ->
                   ValuePath (tm_subst_tm_tm b x a) F.
Proof. intros. induction H; simpl; eauto. econstructor; eauto with lngen lc.
Qed.

Lemma ValuePath_subst_co : forall F a b c, ValuePath a F -> lc_co b ->
                   ValuePath (co_subst_co_tm b c a) F.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma tm_pattern_agree_subst_tm : forall a p b x, lc_tm b -> tm_pattern_agree a p ->
                         tm_pattern_agree (tm_subst_tm_tm b x a) p.
Proof. intros.
       induction H0; simpl; eauto. econstructor.
       eapply tm_subst_tm_tm_lc_tm; eauto. auto. econstructor.
       eapply tm_subst_tm_tm_lc_tm; eauto. auto.
Qed.

Lemma tm_pattern_agree_subst_co : forall a p g c, lc_co g -> tm_pattern_agree a p ->
                         tm_pattern_agree (co_subst_co_tm g c a) p.
Proof. intros.
       induction H0; simpl; eauto. econstructor.
       eapply co_subst_co_tm_lc_tm; eauto. auto. econstructor.
       eapply co_subst_co_tm_lc_tm; eauto. auto.
Qed.

Lemma tm_subpattern_agree_subst_tm : forall a p b x, lc_tm b ->
      tm_subpattern_agree a p -> tm_subpattern_agree (tm_subst_tm_tm b x a) p.
Proof. intros. induction H0; eauto. econstructor.
       eapply tm_pattern_agree_subst_tm; eauto.
Qed.

Lemma tm_subpattern_agree_subst_co : forall a p g c, lc_co g ->
      tm_subpattern_agree a p -> tm_subpattern_agree (co_subst_co_tm g c a) p.
Proof. intros. induction H0; eauto. econstructor.
       eapply tm_pattern_agree_subst_co; eauto.
Qed.

Lemma subtm_pattern_agree_subst_tm : forall a p b x, lc_tm b ->
      subtm_pattern_agree a p -> subtm_pattern_agree (tm_subst_tm_tm b x a) p.
Proof. intros. induction H0; simpl. econstructor.
       eapply tm_pattern_agree_subst_tm; eauto.
       eauto with lngen lc. eauto with lngen lc.
Qed.

Lemma subtm_pattern_agree_subst_co : forall a p g c, lc_co g ->
      subtm_pattern_agree a p -> subtm_pattern_agree (co_subst_co_tm g c a) p.
Proof. intros. induction H0; simpl. econstructor.
       eapply tm_pattern_agree_subst_co; eauto.
       eauto with lngen lc. eauto with lngen lc.
Qed.



Lemma role_dec : forall (R1 : role) R2, R1 = R2 \/ ~(R1 = R2).
Proof. intros. destruct R1, R2; auto. right. intro. inversion H.
       right. intro. inversion H.
Qed.

Lemma match_bullet : forall a p b, MatchSubst a p a_Bullet b -> b = a_Bullet.
Proof. intros. dependent induction H; auto.
       pose (P := IHMatchSubst ltac:(auto)). rewrite P. auto.
Qed.

Lemma match_dec : forall a p, lc_tm a -> MatchSubst a p a_Bullet a_Bullet \/ ~(MatchSubst a p a_Bullet a_Bullet).
Proof. intros. generalize dependent a.
       induction p; intros; try (right; intro P; inversion P; fail).
        - destruct nu. destruct a; try (right; intro P; inversion P; fail).
           + destruct nu; try (right; intro P; inversion P; fail).
             destruct p2; try (right; intro P; inversion P; fail).
             pose (P := role_dec R0 R). inversion P; subst.
              * inversion H; subst. pose (Q := IHp1 a1 H2). inversion Q.
                  ** assert (Q' : a_Bullet = (tm_subst_tm_tm a2 x a_Bullet)).
                    {auto. }
                    left. apply MatchSubst_AppRelR with
                    (R := R)(a := a2)(x := x) in H0. rewrite <- Q' in H0. auto.
                    auto.
                  ** right. intro Q1. inversion Q1; subst. rewrite H10 in H11.
                     pose (Q2 := H11). apply match_bullet in Q2. subst.
                     contradiction.
              * right; intro P1; inversion P1; contradiction.
           + destruct rho. right; intro P1; inversion P1.
             destruct p2; try (right; intro P; inversion P; fail).
             destruct a; try (right; intro P; inversion P; fail).
             destruct nu; try (right; intro P; inversion P; fail).
             destruct rho; try (right; intro P1; inversion P1; fail).
             inversion H; subst. pose (Q := IHp1 a1 H2). inversion Q.
             left; eauto. right. intro P. inversion P. contradiction.
        - destruct g; try (right; intro P; inversion P; fail).
          destruct a; try (right; intro P; inversion P; fail).
          destruct g; try (right; intro P; inversion P; fail).
          inversion H; subst. pose (Q := IHp a H2). inversion Q.
          left; eauto. right. intro P. inversion P. contradiction.
        - destruct a; try (right; intro P; inversion P; fail).
          destruct (F0 == F). subst. left. eauto.
          right; intro P; inversion P; contradiction.
Qed.


Fixpoint var_patt (p : tm) : atoms := 
   match p with
      a_App p (Role R) (a_Var_f x) => (singleton x) \u (var_patt p)
    | a_App p (Rho Irrel) Bullet => var_patt p
    | a_CApp p g_Triv => var_patt p
    | _  => {}
   end.

Lemma MatchSubst_subst : forall a p b1 x y b2,
     MatchSubst a p (tm_subst_tm_tm (a_Var_f y) x b1) b2 ->
     y `notin` fv_tm_tm_tm a -> y `notin` var_patt(p) -> x `notin` var_patt(p) ->
     MatchSubst a p b1 (tm_subst_tm_tm (a_Var_f x) y b2).
Proof. intros. dependent induction H.
        - admit.
        - simpl in *. eapply MatchSubst_AppRelR in IHMatchSubst; eauto 2.
          erewrite tm_subst_tm_tm_tm_subst_tm_tm in IHMatchSubst; eauto 2.
          assert (a_Var_f x = tm_subst_tm_tm a x0 (a_Var_f x)).
          simpl. destruct (x == x0); eauto. apply notin_union_1 in H3.
          apply notin_singleton_1 in H3. symmetry in e. contradiction.
          rewrite H4. eauto.
        - simpl in *. eauto.
        - simpl in *. eauto.
Admitted.

Lemma MatchSubst_Rename : forall p1 p2 a1 a2 W W' a b, Rename p1 a1 p2 a2 W W' ->
                                 MatchSubst a p1 a1 b ->
                                 MatchSubst a p2 a2 b.
Proof. intros. generalize dependent p2. generalize dependent a2.
       generalize dependent W. generalize dependent W'. induction H0; intros.
        - inversion H0; subst. eauto.
        - inversion H1; subst. apply IHMatchSubst in H10.
          eapply MatchSubst_AppRelR in H10; auto. admit.
        - inversion H1; subst. eauto.
        - inversion H; subst. eauto.
Admitted.
(*
Lemma subst_CasePath : forall F a b R x, lc_tm b -> Value R a ->
                   CasePath R (tm_subst_tm_tm b x a) F -> CasePath R a F.
Proof. intros. induction a; simpl in H1; auto; try (inversion H1; fail).
        - inversion H0; subst; inversion H2.
        - destruct nu. inversion H1. inversion H1; subst.
          econstructor. admit. inversion H0; subst.
        - inversion H0; subst. inversion H1; subst. inversion H2; subst.
          econstructor. eapply IHa; eauto.
Qed.

Lemma subst_co_Path : forall F a b R c, lc_co b -> Value R a ->
                      RolePath F (co_subst_co_tm b c a) R -> RolePath F a R.
Proof. intros. induction a; simpl in H1; auto; try (inversion H1; fail).
        - inversion H0; subst. inversion H1; subst. inversion H2; subst.
          eauto.
        - inversion H0; subst. inversion H2; subst.
          inversion H1; subst. eauto.
Qed.

Lemma no_Path_reduction : forall R a F, RolePath F a R -> forall b, not (reduction_in_one a b R).
Proof.
  intros R a F H. induction H; simpl; intros.
  all : intros NH; inversion NH; subst.
  - inversion H0; subst. assert (P : Ax b A0 R0 = Cs A).
    eapply binds_unique; eauto using uniq_toplevel. inversion P.
  - inversion H1. subst. assert (P : Ax a A R1 = Ax b A0 R2).
    eapply binds_unique; eauto using uniq_toplevel. inversion P.
    subst. contradiction.
  - pose (Q := IHPath a'); contradiction.
  - inversion H1; subst. inversion H0.
  - pose (Q := IHPath a'); contradiction.
  - inversion H0; subst. inversion H.
Qed.

Lemma sub_Path : forall F a R1 R2, RolePath F a R1 -> SubRole R1 R2 ->
                        RolePath F a R2 \/ (exists a', reduction_in_one a a' R2).
Proof. intros. induction H.
        - left. eauto.
        - destruct (sub_dec R1 R2) as [P1 | P2].
          right. exists a. eauto. left. eauto.
        - apply IHPath in H0. inversion H0 as [P1 | P2].
          left. eauto. right. inversion P2 as [a' Q].
          exists (a_App a' rho R1 b'); eauto.
        - apply IHPath in H0. inversion H0 as [P1 | P2].
          left. eauto. right. inversion P2 as [a' Q].
          exists (a_CApp a' g_Triv); eauto.
Qed.

Lemma nsub_Path : forall F a R1 R2, RolePath F a R1 -> SubRole R2 R1 ->
                        RolePath F a R2.
Proof. intros. induction H.
        - eauto.
        - destruct (sub_dec R1 R2) as [P1 | P2]. eauto. eauto.
        - apply IHPath in H0. eauto.
        - apply IHPath in H0. eauto.
Qed.
*)


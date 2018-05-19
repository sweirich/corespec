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

Lemma CasePath_lc : forall F a R, CasePath R a F -> lc_tm a.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_binds_toplevel : forall F a R, CasePath R a F ->
                     (exists A Rs, binds F (Cs A Rs) toplevel) \/
                     (exists p a0 A0 R0 Rs, binds F (Ax p a0 A0 R0 Rs) toplevel
                                                  /\ ~(SubRole R0 R)).
Proof. intros. induction H. left. exists A, Rs; auto.
       right. exists p, a, A, R1, Rs; auto. auto. auto.
Qed.

Lemma CasePath_subst : forall F a b R x, CasePath R a F -> lc_tm b ->
                   CasePath R (tm_subst_tm_tm b x a) F.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma CasePath_subst_co : forall F a b R c, CasePath R a F -> lc_co b ->
                   CasePath R (co_subst_co_tm b c a) F.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
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
          destruct nu; try (right; intro P; inversion P; fail).
          destruct p2; try (right; intro P; inversion P; fail).
          pose (P := role_dec R0 R). inversion P. subst.
          inversion H; subst. pose (Q := IHp1 a1 H2). inversion Q.
          assert (Q' : a_Bullet = (tm_subst_tm_tm a2 x a_Bullet)). {auto. }
          left. apply MatchSubst_AppRelR with (R := R)(a := a2)(x := x) in H0.
          rewrite <- Q' in H0. auto. auto.
          right. intro Q1. inversion Q1; subst. rewrite H10 in H11.
          pose (Q2 := H11). apply match_bullet in Q2. subst. contradiction.
          right; intro P1; inversion P1; contradiction.
          destruct rho. right; intro P1; inversion P1.
          destruct p2; try (right; intro P; inversion P; fail).
          destruct a; try (right; intro P; inversion P; fail).
          destruct nu; try (right; intro P; inversion P; fail).
          destruct rho; try (right; intro P1; inversion P1; fail).
          destruct a2; try (right; intro P; inversion P; fail).
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

Lemma CasePath_ValuePath : forall R a F, CasePath R a F -> ValuePath a F.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_Value : forall R a F, CasePath R a F -> Value R a.
Proof. intros. pose (P := CasePath_binds_toplevel H).
       inversion P as [[A [Rs Q]] | [p [a0 [A0 [R0 [Rs [Q1 Q2]]]]]]].
       pose (Q' := H). apply CasePath_ValuePath in Q'. eauto.
       pose (Q' := H). apply CasePath_ValuePath in Q'.
       pose (Q3 := match_dec). pose (Q4 := Q3 a p (CasePath_lc H)).
       inversion Q4; eauto.
Qed.
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
                      Path F (co_subst_co_tm b c a) R -> Path F a R.
Proof. intros. induction a; simpl in H1; auto; try (inversion H1; fail).
        - inversion H0; subst. inversion H1; subst. inversion H2; subst.
          eauto.
        - inversion H0; subst. inversion H2; subst.
          inversion H1; subst. eauto.
Qed.

Lemma no_Path_reduction : forall R a F, Path F a R -> forall b, not (reduction_in_one a b R).
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

Lemma sub_Path : forall F a R1 R2, Path F a R1 -> SubRole R1 R2 ->
                        Path F a R2 \/ (exists a', reduction_in_one a a' R2).
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

Lemma nsub_Path : forall F a R1 R2, Path F a R1 -> SubRole R2 R1 ->
                        Path F a R2.
Proof. intros. induction H.
        - eauto.
        - destruct (sub_dec R1 R2) as [P1 | P2]. eauto. eauto.
        - apply IHPath in H0. eauto.
        - apply IHPath in H0. eauto.
Qed.

Lemma decide_Path : forall W a R, roleing W a R -> (exists F, Path F a R) \/
                                     (forall F, not (Path F a R)).
Proof.
  induction a; intros R' E.
  all: try solve [right; move => F h1; inversion h1].
  - inversion E; subst. apply IHa1 in H5. destruct H5 as [[F h0]|n].
    left. exists F. econstructor; auto. eapply roleing_lc; eauto.
    right. intros. intro. inversion H; subst. pose (Q := n F). contradiction.
  - inversion E; subst. left. exists F; eauto.
    destruct (sub_dec R R') as [P1 | P2].
    right. intros. intro. inversion H; subst.
    have Q: (Ax a A R = Cs A0).
    eapply binds_unique; eauto using uniq_toplevel.
    inversion Q.
    have Q: (Ax a A R = Ax a0 A0 R1).
    eapply binds_unique; eauto using uniq_toplevel.
    inversion Q. subst. contradiction. left. exists F. eauto.
  - inversion E; subst. apply IHa in H3. destruct H3 as [[F h0]|n].
    left. exists F. eauto. right. intros. intro. inversion H; subst.
    pose (Q := n F). contradiction.
Qed.

Lemma Path_dec : forall W a R F, roleing W a R -> Path F a R \/ ~Path F a R.
Proof. induction a; intros R' E.
       all: try solve [right; move => h1; inversion h1].
        - intros. inversion H; subst. pose (P := IHa1 R' E H6).
          inversion P as [P1 | P2]. left; econstructor.
          eapply roleing_lc; eauto. auto. right. intro.
          inversion H0; subst. contradiction.
        - intros. inversion H; subst. destruct (E == F). subst.
          left. eauto. right. intro. inversion H0; subst.
          contradiction. contradiction.
          pose (P := sub_dec R R').
          inversion P as [P1 | P2]. right. intro. inversion H0; subst.
          assert (Q : Ax a A R = Cs A0). eapply binds_unique; eauto.
          eapply uniq_toplevel. inversion Q.
          assert (Ax a A R = Ax a0 A0 R1). eapply binds_unique; eauto.
          eapply uniq_toplevel. inversion H2; subst. contradiction.
          destruct (E == F). subst. left. eauto. right. intro.
          inversion H0; subst. contradiction. contradiction.
        - intros. inversion H; subst. pose (P := IHa R' E H4).
          inversion P as [P1 | P2]. left; eauto.
          right. intro. inversion H0; subst. contradiction.
Qed. *)
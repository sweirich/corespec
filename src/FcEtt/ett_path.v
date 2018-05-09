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

Lemma Path_binds_toplevel : forall F a R, ValuePath R a F ->
                     (exists A Rs, binds F (Cs A Rs) toplevel) \/
                     (exists p a0 A0 R0 Rs, binds F (Ax p a0 A0 R0 Rs) toplevel
                                                  /\ ~(SubRole R0 R)).
Proof. intros. induction H. left. exists A, Rs; auto.
       right. exists p, a, A, R1, Rs; auto. auto. auto.
Qed.

Lemma Path_subst : forall F a b R x, ValuePath R a F -> lc_tm b ->
                   ValuePath R (tm_subst_tm_tm b x a) F.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma Path_subst_co : forall F a b R c, ValuePath R a F -> lc_co b ->
                   ValuePath R (co_subst_co_tm b c a) F.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.
(*
Lemma subst_Path : forall F a b R x, lc_tm b -> Value R a ->
                   ValuePath R (tm_subst_tm_tm b x a) F -> ValuePath R a F.
Proof. intros. induction a; simpl in H1; auto; try (inversion H1; fail).
        - inversion H0. inversion H2. inversion H3.
        - destruct nu. inversion H1.
          inversion H2; subst. inversion H2; subst.
          econstructor. auto. eapply IHa1; eauto.
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
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Import FcEtt.ett_value.

Lemma Path_lc : forall F a R, Path F a R -> lc_tm a.
Proof. intros. induction H; auto.
Qed.

Lemma Path_binds_toplevel : forall F a R, Path F a R -> exists a0 A0 R0,
                                   binds F (Ax a0 A0 R0) toplevel.
Proof. intros. induction H. exists a, A, R1; auto. auto. auto.
Qed.

Lemma Path_subst : forall F a b R x, Path F a R -> lc_tm b ->
                   Path F (tm_subst_tm_tm b x a) R.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma Path_subst_co : forall F a b R c, Path F a R -> lc_co b ->
                   Path F (co_subst_co_tm b c a) R.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma subst_Path : forall F a b R x, lc_tm b -> Value R a ->
                   Path F (tm_subst_tm_tm b x a) R -> Path F a R.
Proof. intros. induction a; simpl in H1; auto; try (inversion H1; fail).
        - inversion H0. inversion H2.
        - inversion H0; subst. inversion H1; subst. inversion H2; subst.
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
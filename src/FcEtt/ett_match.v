Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.fix_typing.

Lemma match_subst_lc1 : forall a p b b', MatchSubst a p b b' -> lc_tm a.
Proof. intros. induction H; auto.
Qed.

Lemma match_subst_lc2 : forall a p b b', MatchSubst a p b b' -> lc_tm b.
Proof. intros. induction H; auto.
Qed.

Lemma match_subst_lc3 : forall a p b b', MatchSubst a p b b' -> lc_tm b'.
Proof. intros. induction H.
        - auto.
        - apply tm_subst_tm_tm_lc_tm; auto.
        - apply tm_subst_tm_tm_lc_tm; auto.
        - apply tm_subst_tm_tm_lc_tm; auto.
        - apply co_subst_co_tm_lc_tm; auto.
Qed.

Lemma apply_args_lc : forall a b c, ApplyArgs a b c -> lc_tm c.
Proof. intros. induction H; auto.
Qed.

Lemma ax_const_rs : forall F F0 a A R Rs S, Sig S ->
                 binds F (Ax (a_Fam F0) a A R Rs) S -> Rs = nil.
Proof. intros. induction H. inversion H0. inversion H0.
       inversion H3. eauto. inversion H0. inversion H5; subst.
       inversion H2; auto. eauto.
Qed.

Lemma match_path : forall F p a A R Rs a0 b, binds F (Ax p a A R Rs) toplevel ->
                          MatchSubst a0 p a b -> Path a0 F nil.
Proof. intros. induction H0.

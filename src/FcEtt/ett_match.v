Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

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

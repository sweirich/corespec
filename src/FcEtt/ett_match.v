Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Lemma match_subst_lc : forall a p b b', MatchSubst a p b b' -> lc_tm a ->
                                        lc_tm b -> lc_tm b'.
Proof. intros. induction H.
        - auto.
        - inversion H0; subst. apply tm_subst_tm_tm_lc_tm; auto.
        - inversion H0; subst. apply tm_subst_tm_tm_lc_tm; auto.
        - inversion H0; subst. apply tm_subst_tm_tm_lc_tm; auto.
        - inversion H0; subst. apply co_subst_co_tm_lc_tm; auto.
Qed.

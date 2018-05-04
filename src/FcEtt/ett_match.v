Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.fix_typing.


Lemma MatchSubst_lc_1 : forall a p b b', MatchSubst a p b b' →  lc_tm a.
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_2 : forall a p b b', MatchSubst a p b b' →  lc_tm b.
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_3 : forall a p b b', MatchSubst a p b b' →  lc_tm b'.
Proof.
  induction 1;
    eauto using tm_subst_tm_tm_lc_tm, co_subst_co_tm_lc_tm.
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

Lemma ApplyArgs_lc_3 : forall a b c, ApplyArgs a b c → lc_tm c.
Proof.
  induction 1; lc_solve.
Qed.

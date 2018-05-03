Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.


(* TODO: where? *)
Generalizable All Variables.

Lemma MatchSubst_lc_1 : `(MatchSubst a p b b' →  lc_tm a).
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_2 : `(MatchSubst a p b b' →  lc_tm b).
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_3 : `(MatchSubst a p b b' →  lc_tm b').
Proof.
  induction 1;
    eauto using tm_subst_tm_tm_lc_tm, co_subst_co_tm_lc_tm.
Qed.


Lemma ApplyArgs_lc_3 : `(ApplyArgs a b c → lc_tm c).
Proof.
  induction 1; lc_solve.
Qed.
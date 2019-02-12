Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.notations.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Import FcEtt.utils.

Require Export FcEtt.fix_typing.


(**** Facts about toplevel signatures ****)

(* --------------------------------------------------- *)

Lemma uniq_toplevel : uniq toplevel.
Proof.
  induction Sig_toplevel; auto.
Qed.

(* ------------------------------------------ *)
Lemma toplevel_inversion : forall F flags a A R Rs, binds F (Ax flags a A R Rs) toplevel ->
                                 (∅ ⊨ a : A /\ ∅; flags ⊨ a : R).
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  - intros. by withf binds do inv.
  - intros. eapply IHst. with binds do invs.
    by with eq do inv.
    by eauto.
  - intros.
    withf binds do invs.
    with eq do invs.
    by ok.
    by eauto.
Qed.

Lemma toplevel_closed_const : forall F A Rs, binds F (Cs A Rs) toplevel ->
                                 Typing nil A a_Star.
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  - intros. inversion H.
  - intros.
    withf binds do inv.
    with eq do inv.
    by subst; eauto.
    by eauto.
  - intros. eapply IHst.
    withf binds do inv.
    with eq do inv.
    by eauto.
Qed.


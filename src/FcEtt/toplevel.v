Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
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
Lemma toplevel_inversion : forall F p a A R Rs, binds F (Ax p a A R Rs) toplevel ->
                                 (exists W G B, PatternContexts W G F A p B /\
                                Typing G a B /\ roleing W a R /\ Rs = range W /\ Typing nil A a_Star).
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  - intros. inversion H.
  - intros. eapply IHst. inversion H1; subst.
    inversion H2. eauto.
  - intros.
    match goal with [ H : binds ?F _ _ |- _ ] => inversion H end.
    match goal with [ H : (_,_) = (_,_) |- _ ] => inversion H end.
    subst. exists W, G, B. eauto. eauto.
Qed.

Lemma toplevel_closed_const : forall F A Rs, binds F (Cs A Rs) toplevel ->
                                 Typing nil A a_Star.
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  - intros. inversion H.
  - intros.
    match goal with [ H : binds ?F _ _ |- _ ] => inversion H end.
    match goal with [ H : (_,_) = (_,_) |- _ ] => inversion H end.
    subst. eauto. eauto.
  - intros. eapply IHst.
    match goal with [ H : binds ?F _ _ |- _ ] => inversion H end.
    match goal with [ H : (_,_) = (_,_) |- _ ] => inversion H end.
    eauto.
Qed.


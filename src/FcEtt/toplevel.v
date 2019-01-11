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
(*
Lemma uniq_an_toplevel : uniq an_toplevel.
Proof.
 induction AnnSig_an_toplevel; auto.
Qed. *)
Lemma uniq_toplevel : uniq toplevel.
Proof.
  induction Sig_toplevel; auto.
Qed.

Lemma PatCtx_lcp : forall W G F p A B, PatternContexts W G F A p B -> lc_tm p.
Proof. intros. induction H; eauto.
Qed.

(* ------------------------------------------ *)
Lemma toplevel_inversion : forall F p a A R Rs, binds F (Ax p a A R Rs) toplevel ->
                                 (exists W G B, PatternContexts W G F A p B /\
                                Typing G a B /\ roleing W a R /\ Rs = range W).
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

Lemma pat_ctx_fv : forall W G F A p B, PatternContexts W G F A p B ->
                                       dom W [<=] fv_tm_tm_tm p.
Proof. intros. induction H; simpl; fsetdec.
Qed.

Lemma pat_ctx_vars_Pattern : forall W G F A p B, PatternContexts W G F A p B ->
            vars_Pattern p = rev (List.map fst W).
Proof. intros. induction H; eauto. simpl. rewrite IHPatternContexts.
       unfold one. auto.
Qed.

Lemma uniq_NoDup : forall (l : role_context), uniq l -> NoDup (List.map fst l).
Proof. intros. induction H; simpl. apply NoDup_nil. apply NoDup_cons.
       intro. apply H0. clear - H1. induction E; eauto. simpl in *.
       inversion H1. destruct a. simpl in H. rewrite H. eauto.
       destruct a. apply IHE in H. auto. auto. Unshelve. exact.
Qed.

Lemma NoDup_add : forall A (l1 l2 : list A) (a : A), ~(In a (l1 ++ l2)) ->
      NoDup (l1 ++ l2) -> NoDup (l1 ++ a :: l2).
Proof. intros. generalize dependent l2. generalize a.
       induction l1; intros; simpl in *.
       apply NoDup_cons; auto. inversion H0; subst. apply NoDup_cons.
       intro. apply in_app_or in H1. inversion H1. apply H3.
       apply in_or_app. left; auto. simpl in H2. inversion H2.
       subst. apply H. left; auto. apply H3. apply in_or_app. right; auto. eauto.
Qed.

Lemma NoDup_reverse : forall A (l : list A), NoDup l -> NoDup (rev l).
Proof. intros. induction H; simpl. apply NoDup_nil. apply NoDup_add.
       rewrite app_nil_r. intro. apply H. apply in_rev in H1. auto.
       rewrite app_nil_r. auto.
Qed.

(*

Lemma toplevel_closed_const : forall F A, binds F (Cs A) toplevel ->
                                 Typing nil A a_Star Rep.
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  - intros. inversion H.
  - intros.
    match goal with [ H : binds ?F _ _ |- _ ] => inversion H end.
    match goal with [ H : (_,_) = (_,_) |- _ ] => inversion H end.
    subst. eauto. eauto.
  - intros. eapply IHst. inversion H1; subst.
    inversion H2. eauto.
Qed.


Lemma an_toplevel_closed : forall F a A R, binds F (Ax a A R) an_toplevel ->
                                    AnnTyping nil a A R.
Proof.
  have st: AnnSig an_toplevel by apply AnnSig_an_toplevel.
  induction st.
  - intros. inversion H.
  - intros.
    match goal with [ H : binds ?F _ _ |- _ ] => inversion H end.
    match goal with [ H : (_,_) = (_,_) |- _ ] => inversion H end.
    subst. eauto. eauto.
Qed. *)

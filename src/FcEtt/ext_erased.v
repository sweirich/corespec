Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Import FcEtt.ext_wf.
Require Import FcEtt.erase_syntax.
Require Export FcEtt.toplevel.
Require Import Metalib.CoqEqDec.

Lemma typing_erased_mutual:
    (forall G psi b A, Typing G psi b A -> erased_tm b) /\
    (forall G0 psi phi (H : PropWff G0 psi phi), erased_constraint phi) /\
     (forall G0 psi p1 p2 (H : Iso G0 psi p1 p2), True ) /\
     (forall G0 psi phi (H : DefEq G0 psi phi), True) /\
      (forall G0 (H : Ctx G0), True) /\
    (forall G0 psi psi0 A B T (H : CDefEq G0 psi psi0 A B T), True).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  (* all : try solve [inversion H2; subst; auto]. *)
  all : try solve [econstructor; eauto].
Qed.

Lemma Typing_erased_tm: forall G psi b A, Typing G psi b A -> erased_tm b.
Proof.
  apply typing_erased_mutual.
Qed.

Lemma Typing_erased_constraint: forall G0 psi phi (H : PropWff G0 psi phi), erased_constraint phi.
Proof.
  apply typing_erased_mutual.
Qed.

Hint Resolve Typing_erased_tm Typing_erased_constraint : erased.


Ltac erased_pick_fresh x :=
  match goal with
    [ |- erased_tm ?s ] =>
    let v := match s with
             | a_UAbs _ _  => erased_a_Abs
             | a_Pi _ _ _  => erased_a_Pi
             | a_CPi _ _ _   => erased_a_CPi
             | a_UCAbs _ _   => erased_a_CAbs
             end
    in pick fresh x and apply v
  | [ |- erased_constraint ?phi ] =>
    let v := match phi with
             | Impl _ _ => erased_c_Impl
             end
    in pick fresh x and apply v
  end.

Ltac erased_inversion :=
  repeat match goal with
  | [H : erased_constraint (Eq _ _ _) |- _] =>
    inversion H; subst; clear H
  | [H : erased_constraint (Impl _ _) |- _] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_UAbs _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_App _ _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_Pi _ _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_CPi _ _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_UCAbs _ _ ) |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_CApp _ _)|- _ ] =>
    inversion H; subst; clear H
end.

Ltac erased_case :=
  let x := fresh in
  let h0 := fresh in
  erased_pick_fresh x; eauto using lc_erase;
  match goal with
    [ H : forall x, erased_tm (erase (open_tm_wrt_tm ?b (a_Var_f x))) |- _ ] =>
    move: (H x) => h0; rewrite <- open_tm_erase_tm in h0; eauto
  | [ H : ∀ c, erased_tm (erase (open_tm_wrt_co ?b (g_Var_f c))) |- _ ] =>
    move: (H x) => h0; rewrite <- open_co_erase_tm2 with (g := (g_Var_f x)) in h0; auto
  end.

Inductive erased_sort : sort -> Prop :=
| erased_Tm : forall a, erased_tm a -> erased_sort (Tm a)
| erased_Co : forall phi, erased_constraint phi -> erased_sort (Co phi).

Definition erased_context : context -> Prop :=
  Forall (fun p => match p with (a,(psi,s)) => erased_sort s end).

Lemma erased_lc : (forall a, erased_tm a -> lc_tm a) /\ (forall phi, erased_constraint phi -> lc_constraint phi).
  eapply erased_tm_constraint_mutual; intros; auto.
Qed.

Lemma erased_lc_tm : forall a, erased_tm a -> lc_tm a.
Proof.
  apply erased_lc.
Qed.

Lemma erased_lc_constraint : forall phi, erased_constraint phi -> lc_constraint phi.
Proof.
  apply erased_lc.
Qed.

Hint Resolve erased_lc_tm : lc.
Hint Resolve erased_lc_constraint : lc.



Lemma subst_tm_erased : (forall a , erased_tm a -> forall x b, erased_tm b -> erased_tm (tm_subst_tm_tm b x a)) /\
                        (forall phi, erased_constraint phi -> forall x b, erased_tm b -> erased_constraint (tm_subst_tm_constraint b x phi)).
Proof.
  apply erased_tm_constraint_mutual; intros; simpl; eauto with lc.
  all: try solve [erased_pick_fresh x0; autorewrite with subst_open_var; eauto with lc].
  - hauto l: on use: eq_dec.
Qed.


Lemma subst_co_erased_mutual : forall c g , lc_co g -> (forall a, erased_tm a -> erased_tm (co_subst_co_tm g c a)) /\
                                          (forall phi, erased_constraint phi -> erased_constraint (co_subst_co_constraint g c phi)).
Proof.
  intros until 1; eapply erased_tm_constraint_mutual; simpl; intros; eauto with lc.
  all: try solve [erased_pick_fresh x0; autorewrite with subst_open_var; eauto using erased_lc].
  (* destruct rho. *)
  (*   + pick fresh y and apply erased_a_Abs; eauto. *)
  (*   assert (W: y `notin` L). fsetdec. apply H0 in W. *)
  (*   rewrite co_subst_co_tm_open_tm_wrt_tm in W. simpl in W. *)
  (*   eauto. eauto. *)
  (*   + pick fresh y and apply erased_a_Abs; eauto. *)
  (*   assert (W: y `notin` L). fsetdec. apply H0 in W. *)
  (*   rewrite co_subst_co_tm_open_tm_wrt_tm in W. simpl in W. *)
  (*   eauto. eauto. assert (W: y `notin` L). fsetdec. apply r in W. *)
  (*   apply Rho_IrrRel. inversion W; subst. *)
  (*   rewrite co_subst_co_tm_open_tm_wrt_tm_var; eauto. apply fv_tm_tm_tm_co_subst_co_tm_notin. *)
  (*   auto with lc. fsetdec. *)
Qed.

Lemma subst_co_erased_tm : forall a c g , lc_co g -> erased_tm a -> erased_tm (co_subst_co_tm g c a).
Proof.
  sfirstorder use:subst_co_erased_mutual.
Qed.
  
Lemma subst_co_erased_constraint : forall phi c g , lc_co g -> erased_constraint phi -> erased_constraint (co_subst_co_constraint g c phi).
Proof.
  sfirstorder use:subst_co_erased_mutual.
Qed.
  
  

Hint Resolve (proj1 subst_tm_erased) (proj2 subst_tm_erased) subst_co_erased_tm subst_co_erased_constraint : erased.

Lemma erased_a_CAbs_inversion : forall psi b, 
     erased_tm (a_UCAbs psi b) -> forall c, c `notin` fv_co_co_tm b 
  -> erased_tm (open_tm_wrt_co b (g_Var_f c)).
Proof.
  intros. inversion H; subst. pick fresh y.
  rewrite (@co_subst_co_tm_intro y); eauto. apply subst_co_erased_tm; eauto.
Qed.

Lemma Par_lc1 : (forall P psi a a' , Par P psi a a' -> lc_tm a) /\
                (forall P psi phi1 phi2 , ParProp P psi phi1 phi2 -> lc_constraint phi1) /\
                (forall P psi psi0 a b, CPar P psi psi0 a b -> lc_tm a) /\
                (forall P psi psi0 phi1 phi2 , CParProp P psi psi0 phi1 phi2 -> lc_constraint phi1).
Proof.
  apply Par_tm_constraint_mutual; intros; eauto 3 using Grade_lc.
  all: lc_solve.
Qed.


(* FIXME: find a good place for this tactic. *)
(* cannot move this to ett_ind.v because need Toplevel_lc ??? *)
Ltac lc_toplevel_inversion :=
  match goal with
  | [ b : binds ?F _ toplevel |- _ ] =>
    apply Toplevel_lc in b; inversion b; auto
end.


Lemma Par_lc2 : (forall P psi a a' , Par P psi a a' -> lc_tm a') /\
                (forall P psi phi1 phi2 , ParProp P psi phi1 phi2 -> lc_constraint phi2) /\
                (forall P psi psi0 a b, CPar P psi psi0 a b -> lc_tm b) /\
                (forall P psi psi0 phi1 phi2 , CParProp P psi psi0 phi1 phi2 -> lc_constraint phi2).
Proof.
  apply Par_tm_constraint_mutual; intros; eauto 3 using Grade_lc.
  all : lc_solve.
  lc_toplevel_inversion.
Qed.

Lemma Par_lc1_tm : forall P psi a a' , Par P psi a a' -> lc_tm a.
  apply Par_lc1.
Qed.

Lemma ParProp_lc1 : forall P psi phi1 phi2 , ParProp P psi phi1 phi2 -> lc_constraint phi1.
  apply Par_lc1.
Qed.

Lemma Par_lc2_tm : forall P psi a a' , Par P psi a a' -> lc_tm a'.
  apply Par_lc2.
Qed.

Lemma ParProp_lc2 : forall P psi phi1 phi2 , ParProp P psi phi1 phi2 -> lc_constraint phi2.
  apply Par_lc2.
Qed.



Hint Resolve Par_lc1_tm Par_lc2_tm ParProp_lc1 ParProp_lc2 : lc.


Lemma erased_a_Abs_exists : ∀ (psi : grade) (a : tm) x,
                x `notin` fv_tm_tm_tm a
              → erased_tm (open_tm_wrt_tm a (a_Var_f x))
              (* → RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)) *)
              → erased_tm (a_UAbs psi a).
Proof.
  intros. pick fresh y and apply erased_a_Abs.
  rewrite (@tm_subst_tm_tm_intro x); eauto. apply subst_tm_erased; eauto.
  (* eapply rho_swap; eauto. *)
Qed.

Lemma erased_a_Abs_inversion : forall psi a, 
     erased_tm (a_UAbs psi a) -> forall x, x `notin` fv_tm_tm_tm a 
  -> erased_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros. inversion H; subst. pick fresh y. (* split. *)
  rewrite (@tm_subst_tm_tm_intro y); eauto. apply subst_tm_erased; eauto.
  (* eapply rho_swap. assert (Q: y `notin` fv_tm_tm_tm a). fsetdec. apply Q. eauto. eauto. *)
Qed.




Lemma typing_erased_type_mutual  :
    (forall G psi b A, Typing G psi b A -> erased_tm A) /\
    (forall G0 psi phi (H : PropWff G0 psi phi), erased_constraint phi) /\
     (forall G0 psi p1 p2 (H : Iso G0 psi p1 p2), erased_constraint p1 /\ erased_constraint p2) /\
     (forall G0 psi phi (H : DefEq G0 psi phi), erased_constraint phi) /\
     (forall G0 (H : Ctx G0), erased_context G0) /\
     (forall G0 psi psi0 A B T (H : CDefEq G0 psi psi0 A B T), erased_tm A /\ erased_tm B /\ erased_tm T).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  all: unfold erased_context in *.
  all: eauto with erased.
    all: try solve [erased_inversion; pick fresh x;
      rewrite (tm_subst_tm_tm_intro x); auto;
        eapply subst_tm_erased;
        eauto with erased].
  all : try solve [erased_inversion; eauto].
  all : try solve [erased_inversion;
    pick fresh x; rewrite (tm_subst_tm_tm_intro x);auto; econstructor; try (eauto with erased; 
                   match goal with [ |- _ `notin` _] => fsetdec end)].
  all : try solve [constructor;
                   try solve [econstructor; eauto with erased; intros;
                                   move: (H _ H1) => h1;
                                                    inversion h1; auto with erased]].
  all : try solve [erased_inversion; econstructor; eauto;
    apply typing_erased_mutual in t0; auto;
    econstructor;
    intros;
    rewrite e; eauto].

  - eapply Forall_forall in H; eauto. simpl in H. inversion H. auto.
  - inversion H; pick fresh x;
      rewrite (co_subst_co_tm_intro x); auto.
        eauto with erased.
  - unfold binds in b.
    erewrite Forall_forall in H.
    apply H in b.
    inversion b; auto.
  (* only handles one case? *)
  - erased_inversion; pick fresh x; econstructor; eauto; rewrite (tm_subst_tm_tm_intro x);
      eauto;eapply subst_tm_erased; eauto with erased lc lngen.

  -  erased_inversion; pick fresh x; econstructor; eauto; try (rewrite (co_subst_co_tm_intro x);
      eauto; eapply subst_co_erased_tm; eauto with erased lc lngen).

  - erased_inversion; pick fresh x; econstructor; eauto; try (rewrite (co_subst_co_tm_intro x);
      try eapply subst_co_erased_tm; try eapply subst_tm_erased; eauto with erased lc lngen).
  - apply Forall_forall.
    intros s h0. destruct s.
    destruct h0. inversion H1. econstructor.
    eauto with erased.
    eapply Forall_forall in H; eauto. simpl in H. auto.
  - apply Forall_forall.
    intros s h0. destruct s.
    induction p.
    + subst.
      destruct h0. inversion H4. econstructor;  eauto with erased.
      eapply Forall_forall in H; eauto. simpl in H. auto.
    + destruct h0. inversion H1; subst. constructor. assumption.
      apply IHp1; eauto. inversion H0; eauto. right. assumption.
Qed.


Lemma Typing_erased_type : forall G psi b A, Typing G psi b A -> erased_tm A.
Proof. apply typing_erased_type_mutual. Qed.

Hint Resolve Typing_erased_type : erased.

Lemma toplevel_erased1 : forall F psi a A, binds F (psi, (Ax a A)) toplevel -> erased_tm a.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  eauto with erased.
Qed.
Lemma toplevel_erased2 : forall F psi a A, binds F (psi,(Ax a A)) toplevel -> erased_tm A.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  eauto with erased.
Qed.

Hint Resolve toplevel_erased1 toplevel_erased2 : erased.

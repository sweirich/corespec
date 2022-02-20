Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.


Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Import ext_wf.



Require Import FcEtt.erase_syntax.

Require Export FcEtt.toplevel.

Require Export FcEtt.ett_value.


(* ------------------------------------------ *)

(* Synatactic properties about parallel reduction. (Excluding confluence.) *)

(* ------------------------------------------ *)


(* TODO: move these definitions to the OTT file. *)

(* Hint Constructors multipar. *)

Hint Constructors multipar.
Hint Constructors multipar_prop.

(* NOTE: we have a database 'erased' for proving that terms are erased. *)

(* Tactics concerning erased terms. *)

Ltac erased_pick_fresh x :=
  match goal with
    [ |- erased_tm ?s ] =>
    let v := match s with
             | a_UAbs _ _  => erased_a_Abs
             | a_Pi _ _ _  => erased_a_Pi
             | a_CPi _ _   => erased_a_CPi
             | a_UCAbs _   => erased_a_CAbs
             end
    in pick fresh x and apply v
  end.

Ltac erased_inversion :=
  repeat match goal with
  | [H : erased_tm (a_UAbs _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_App _ _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_Pi _ _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_CPi _ _)|- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_UCAbs _ ) |- _ ] =>
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
  Forall (fun p => match p with (a,s) => erased_sort s end).

Definition joins S D a b := exists c, erased_context S /\ erased_tm a /\ erased_tm b /\
                               multipar S D a c /\ multipar S D b c.

Definition joins_constraint S D phi1 phi2 := exists phi3, erased_context S /\
                                                     erased_constraint phi1 /\
                                                     erased_constraint phi2 /\
                                                     multipar_prop S D phi1 phi3 /\ multipar_prop S D phi2 phi3.

Scheme erased_tm_ind' := Induction for erased_tm Sort Prop
   with erased_constraint_ind' := Induction for erased_constraint Sort Prop.

Combined Scheme erased_tm_constraint_mutual from erased_tm_ind', erased_constraint_ind'.


Lemma ParProp_refl : forall G D phi, lc_constraint phi -> ParProp G D phi phi.
Proof.
  induction phi; inversion 1;auto.
Qed.

(* YL: Should I add refl rule to ParProp? *)
Hint Resolve ParProp_refl.


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
  eapply erased_tm_constraint_mutual; intros; simpl; eauto with lc.
  all: try solve [erased_pick_fresh x0; autorewrite with subst_open_var; eauto with lc].
  - destruct eq_dec; eauto.
  - destruct rho.
    + pick fresh y and apply erased_a_Abs; eauto.
      assert (W: y `notin` L). fsetdec. apply H  with (x := y) (x0 := x) (b := b) in W.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in W. simpl in W.
      assert (Q: (if y == x then b else a_Var_f y) = (a_Var_f y)).
      destruct (y == x). fsetdec. eauto. rewrite Q in W. eauto.
      apply erased_lc; eauto.
      assumption.
    + pick fresh y and apply erased_a_Abs; eauto.
      assert (W: y `notin` L). fsetdec. apply H with (x := y) (x0 := x) (b := b) in W.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm in W. simpl in W.
      assert (Q: (if y == x then b else a_Var_f y) = (a_Var_f y)).
      destruct (y == x). fsetdec. eauto. rewrite Q in W. eauto.
      apply erased_lc; eauto. assumption.
      assert (W: y `notin` L). fsetdec. apply r in W.
      apply Rho_IrrRel. inversion W; subst.
      rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; eauto. apply fv_tm_tm_tm_tm_subst_tm_tm_notin.
      auto. fsetdec. apply erased_lc; auto.
Qed.


Lemma erased_a_Abs_exists : ∀  (rho : relflag) (a : tm) x,
                x `notin` fv_tm_tm_tm a
              → erased_tm (open_tm_wrt_tm a (a_Var_f x))
              → RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x))
              → erased_tm (a_UAbs rho a).
Proof.
  intros. pick fresh y and apply erased_a_Abs.
  rewrite (@tm_subst_tm_tm_intro x); eauto. apply subst_tm_erased; eauto.
  eapply rho_swap; eauto.
Qed.

Lemma erased_a_Abs_inversion : forall rho a, 
     erased_tm (a_UAbs rho a) -> forall x, x `notin` fv_tm_tm_tm a 
  -> erased_tm (open_tm_wrt_tm a (a_Var_f x)) /\ RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros. inversion H; subst. pick fresh y. split.
  rewrite (@tm_subst_tm_tm_intro y); eauto. apply subst_tm_erased; eauto.
  eapply rho_swap. assert (Q: y `notin` fv_tm_tm_tm a). fsetdec. apply Q. eauto. eauto.
Qed.

Lemma subst_co_erased_mutual : forall c g , lc_co g -> (forall a, erased_tm a -> erased_tm (co_subst_co_tm g c a)) /\
                                          (forall phi, erased_constraint phi -> erased_constraint (co_subst_co_constraint g c phi)).
Proof.
  intros until 1; eapply erased_tm_constraint_mutual; simpl; intros; eauto with lc.
  all: try solve [erased_pick_fresh x0; autorewrite with subst_open_var; eauto using erased_lc].
  destruct rho.
    + pick fresh y and apply erased_a_Abs; eauto.
    assert (W: y `notin` L). fsetdec. apply H0 in W.
    rewrite co_subst_co_tm_open_tm_wrt_tm in W. simpl in W.
    eauto. eauto.
    + pick fresh y and apply erased_a_Abs; eauto.
    assert (W: y `notin` L). fsetdec. apply H0 in W.
    rewrite co_subst_co_tm_open_tm_wrt_tm in W. simpl in W.
    eauto. eauto. assert (W: y `notin` L). fsetdec. apply r in W.
    apply Rho_IrrRel. inversion W; subst.
    rewrite co_subst_co_tm_open_tm_wrt_tm_var; eauto. apply fv_tm_tm_tm_co_subst_co_tm_notin.
    auto with lc. fsetdec.
Qed.

Lemma subst_co_erased_tm : forall a c g , lc_co g -> erased_tm a -> erased_tm (co_subst_co_tm g c a).
Proof.
  intros a c g H.
  generalize a.
  eapply proj1.
  apply subst_co_erased_mutual.
  assumption.
Qed.
  
Lemma subst_co_erased_constraint : forall phi c g , lc_co g -> erased_constraint phi -> erased_constraint (co_subst_co_constraint g c phi).
Proof.
  intros a c g H.
  generalize a.
  eapply proj2.
  apply subst_co_erased_mutual.
  assumption.
Qed.
  
  

Hint Resolve (proj1 subst_tm_erased) (proj2 subst_tm_erased) subst_co_erased_tm subst_co_erased_constraint : erased.

Lemma erased_a_CAbs_inversion : forall b, 
     erased_tm (a_UCAbs b) -> forall c, c `notin` fv_co_co_tm b 
  -> erased_tm (open_tm_wrt_co b (g_Var_f c)).
Proof.
  intros. inversion H; subst. pick fresh y.
  rewrite (@co_subst_co_tm_intro y); eauto. apply subst_co_erased_tm; eauto.
Qed.

Scheme Par_ind' := Induction for Par Sort Prop
   with ParProp_ind' := Induction for ParProp Sort Prop.

Combined Scheme Par_tm_constraint_mutual from Par_ind', ParProp_ind'.

Lemma Par_lc1 : (forall G D a a' , Par G D a a' -> lc_tm a) /\ (forall G D phi phi' , ParProp G D phi phi' -> lc_constraint phi).
  apply Par_tm_constraint_mutual; intros; auto.
  all: lc_solve.
Qed.

(* FIXME: find a good place for this tactic. *)
(* cannot move this to ett_ind.v because need Toplevel_lc ??? *)
Ltac lc_toplevel_inversion :=
  match goal with
  | [ b : binds ?F _ toplevel |- _ ] =>
    apply Toplevel_lc in b; inversion b; auto
end.

Lemma Par_lc2 : (forall G D a a' , Par G D a a' -> lc_tm a') /\ (forall G D phi phi' , ParProp G D phi phi' -> lc_constraint phi').
Proof.
  apply Par_tm_constraint_mutual; intros; auto.
  - lc_solve.
  - lc_solve.
  - lc_solve.
  - lc_toplevel_inversion.
Qed.

Lemma Par_lc1_tm : forall G D a a' , Par G D a a' -> lc_tm a.
  apply Par_lc1.
Qed.

Lemma Par_lc2_tm : forall G D a a' , Par G D a a' -> lc_tm a'.
  apply Par_lc2.
Qed.


Hint Resolve (proj1 Par_lc1) (proj1 Par_lc2) (proj2 Par_lc1) (proj2 Par_lc2) : lc.

Lemma typing_erased_mutual:
    (forall G b A, Typing G b A -> erased_tm b) /\
    (forall G0 phi (H : PropWff G0 phi), erased_constraint phi) /\
     (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\
     (forall G0 D phi (H : DefEq G0 D phi), True) /\
     (forall G0 (H : Ctx G0), True).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  all : try solve [inversion H2; subst; auto].
  all : try solve [econstructor; eauto].
Qed.

Lemma Typing_erased_tm: forall G b A, Typing G b A -> erased_tm b.
Proof.
  apply typing_erased_mutual.
Qed.

Lemma Typing_erased_constraint: forall G0 phi (H : PropWff G0 phi), erased_constraint phi.
Proof.
  apply typing_erased_mutual.
Qed.

Hint Resolve Typing_erased_tm Typing_erased_constraint : erased.

Lemma typing_erased_type_mutual:
    (forall G b A, Typing G b A -> erased_tm A) /\
    (forall G0 phi (H : PropWff G0 phi), erased_constraint phi) /\
     (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\
     (forall G0 D phi (H : DefEq G0 D phi), True) /\
     (forall G0 (H : Ctx G0), erased_context G0).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  all: unfold erased_context in *.
  all: eauto with erased.
    all: try solve [inversion H; pick fresh x;
      rewrite (tm_subst_tm_tm_intro x); auto;
        eapply subst_tm_erased;
        eauto with erased].
  - eapply Forall_forall in H; eauto. simpl in H. inversion H. auto.
  - inversion H; pick fresh x;
      rewrite (co_subst_co_tm_intro x); auto.
        eauto with erased.
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

Lemma Typing_erased_type : forall G b A, Typing G b A -> erased_tm A.
Proof. apply typing_erased_type_mutual. Qed.

Hint Resolve Typing_erased_type : erased.

Lemma toplevel_erased1 : forall F a A, binds F (Ax a A) toplevel -> erased_tm a.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  eauto with erased.
Qed.
Lemma toplevel_erased2 : forall F a A, binds F (Ax a A) toplevel -> erased_tm A.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  eauto with erased.
Qed.

Hint Resolve toplevel_erased1 toplevel_erased2 : erased.


(* Introduce a hypothesis about an erased opened term. *)
Ltac erased_body x Ea :=
    match goal with
     | [ H4 : ∀ x : atom, x `notin` ?L0 → erased_tm (open_tm_wrt_tm ?a (a_Var_f x))
                         |- _ ] =>
      move: (H4 x ltac:(auto)) => Ea; clear H4
     | [ H4 : ∀ x : atom, x `notin` ?L0 → erased_tm (open_tm_wrt_co ?a (g_Var_f x))
                         |- _ ] =>
      move: (H4 x ltac:(auto)) => Ea; clear H4
    end.

(* Move this to ett_ind? *)
Ltac eta_eq y EQ :=
   match goal with
     | [ H : ∀ x : atom, x `notin` ?L → open_tm_wrt_tm ?a (a_Var_f x) =
                           a_App ?b ?rho _ |- _ ] =>
        move: (H y ltac:(auto)) =>  EQ
end.



Lemma Par_fv_preservation: forall x, 
  (forall G D a b, Par G D a b ->
             x `notin` fv_tm_tm_tm a ->
             x `notin` fv_tm_tm_tm b) /\
  (forall G D phi1 phi2, ParProp G D phi1 phi2 ->
             x `notin` fv_tm_tm_constraint phi1 ->
             x `notin` fv_tm_tm_constraint phi2).
Proof.
  move => x.
  apply Par_tm_constraint_mutual; intros; eauto 2; simpl in *.
  all: simpl in H.
  all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto].
  all: try auto.
  - simpl in *.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_tm a' b') => h0.
    apply fv_tm_tm_tm_open_tm_wrt_tm_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec_fast.
    fsetdec_fast.
    auto.
  - rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper.
    fsetdec.
  - have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' g_Triv) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec.
    auto.
  - pick fresh x0.
    assert (Fl : x0 `notin` L). auto.
    assert (Fa : x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x0))).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. auto.
    move: (H x0 Fl Fa) => h0.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. 
  - pick fresh x0.
    have na': x `notin` fv_tm_tm_tm A'. eauto.
    have nb: x `notin` fv_tm_tm_tm (open_tm_wrt_tm B (a_Var_f x0)).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. eauto.
    have nob': x `notin` fv_tm_tm_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto.
    have nb': x `notin` fv_tm_tm_tm B'.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.
    eauto.
  - pick_fresh c0.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have K:= H c0 ltac:(auto) h0.
    move => h1.
    apply K. auto.
    apply fv_tm_tm_tm_open_tm_wrt_co_lower; auto.
  - pick fresh c0 for L.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have h2: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' (g_Var_f c0)). eauto.
    move: (fv_tm_tm_tm_open_tm_wrt_co_lower a' (g_Var_f c0)) => h3. fsetdec.
  - move : b H => H.
    apply toplevel_closed in H.
    move: (Typing_context_fv H) => ?. split_hyp.
    simpl in *.
    fsetdec.
  - move : H e => IHPar H1.
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_tm_tm_tm) in h0.
    simpl in h0.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_tm_tm_tm b) (singleton y))). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. done.
    done.
  - move : H e => IHPar H1.
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_tm_tm_tm) in h0.
    simpl in h0.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1.
    move: (@fv_tm_tm_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_tm_tm_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. done.
    done.
  - move : H e => IHPar H1.
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_tm_tm_tm) in h0.
    simpl in h0.
    move: (@fv_tm_tm_tm_open_tm_wrt_co_lower a (g_Var_f y) x) => h1.
    move: (@fv_tm_tm_tm_open_tm_wrt_co_upper a (g_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_tm_tm_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct H0. 
    apply AtomSetProperties.empty_union_1 in h3.
    auto. done.
Qed.

Lemma Par_fv_co_preservation: forall x, (forall G D a b, Par G D a b ->
                                        x `notin` fv_co_co_tm a ->
                                        x `notin` fv_co_co_tm b) /\
                                   (forall G D phi1 phi2, ParProp G D phi1 phi2 ->
                                        x `notin` fv_co_co_constraint phi1 ->
                                        x `notin` fv_co_co_constraint phi2).
Proof.
  move => x.
  apply Par_tm_constraint_mutual; intros; eauto 2; simpl.
  all: simpl in *.
  all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto].
  all: try auto.
  - simpl in *.
    have: x `notin` fv_co_co_tm (open_tm_wrt_tm a' b') => h0.
    apply fv_co_co_tm_open_tm_wrt_tm_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec_fast.
    fsetdec_fast.
    auto.
  - rewrite fv_co_co_tm_open_tm_wrt_tm_upper.
    fsetdec.
  - have: x `notin` fv_co_co_tm (open_tm_wrt_co a' g_Triv) => h0.
    apply fv_co_co_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec.
    auto.
  - move : H => H1.
    pick fresh x0.
    assert (Fl : x0 `notin` L). auto.
    assert (Fa : x `notin` fv_co_co_tm (open_tm_wrt_tm a (a_Var_f x0))).
    rewrite fv_co_co_tm_open_tm_wrt_tm_upper. auto.
    move: (H1 x0 Fl Fa) => h0.
    rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto. 
  - pick fresh x0.
    have na': x `notin` fv_co_co_tm A'. eauto.
    have nb: x `notin` fv_co_co_tm (open_tm_wrt_tm B (a_Var_f x0)).
    rewrite fv_co_co_tm_open_tm_wrt_tm_upper. eauto.
    have nob': x `notin` fv_co_co_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto.
    have nb': x `notin` fv_co_co_tm B'.
    rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto.
    eauto.
  - move : H => H1.
    pick_fresh c0.
    have: x `notin` fv_co_co_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_co_co_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have K:= H1 c0 ltac:(auto) h0.
    move => h1.
    apply K. auto.
    apply fv_co_co_tm_open_tm_wrt_co_lower; auto.
  - pick fresh c0.
    have: x `notin` fv_co_co_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_co_co_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    destruct_notin.
    simpl in h0. fsetdec.
    simpl in h0. assert (Q: c0 `notin` singleton x). fsetdec.
    destruct_notin.
    have h2: x `notin` fv_co_co_tm (open_tm_wrt_co a' (g_Var_f c0)). eauto.
    move: (fv_co_co_tm_open_tm_wrt_co_lower a' (g_Var_f c0)) => h3.
    have h4: x `notin` fv_co_co_tm a'. fsetdec.
    fsetdec.
  - move : b H => H.             (* rename b to H and remove the original H *)
    apply toplevel_closed in H.
    move: (Typing_context_fv H) => ?. split_hyp.
    simpl in *.
    fsetdec.
  - move : H e => IHPar H1.
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_co_co_tm) in h0.
    simpl in h0.
    move: (@fv_co_co_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1.
    move: (@fv_co_co_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_co_co_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. fsetdec. fsetdec.
  - move : H e => IHPar H1.
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_co_co_tm) in h0.
    simpl in h0.
    move: (@fv_co_co_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1.
    move: (@fv_co_co_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_co_co_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3.
    destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. fsetdec. fsetdec.
  - move : H e => IHPar H1.
    apply IHPar.
    pick fresh y.
    move: (H1 y ltac:(auto)) => h0.
    apply (fun_cong fv_co_co_tm) in h0.
    simpl in h0.
    move: (@fv_co_co_tm_open_tm_wrt_co_lower a (g_Var_f y) x) => h1.
    move: (@fv_co_co_tm_open_tm_wrt_co_upper a (g_Var_f y) x) => h2.
    unfold not. intro IN.
    assert (h3: x `in` (union (fv_co_co_tm b) empty)). auto.
    rewrite -h0 in h3.
    apply h2 in h3.
    simpl in h3. destruct (AtomSetImpl.union_1 h3).
    assert (x `notin` singleton y). auto. fsetdec. fsetdec.
Qed.

Lemma Par_erased_tm_constraint_mutual : (forall G D a a', Par G D a a' -> forall (Ea : erased_tm a), erased_tm a') /\
                      (forall G D phi phi', ParProp G D phi phi' -> forall (Ephi : erased_constraint phi),  erased_constraint phi').
Proof.
  apply Par_tm_constraint_mutual; intros; try inversion Ea; try inversion Ephi; subst; eauto.
  (* intros G D a a' Ep Ea.  induction Ep; inversion Ea; subst; eauto 2. *)
  all: try solve [ erased_pick_fresh x; auto ].
  all: eauto with erased.
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (tm_subst_tm_tm_intro x); auto;
    apply subst_tm_erased; auto.
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (tm_subst_tm_tm_intro x); auto;
    apply subst_tm_erased; auto.
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (co_subst_co_tm_intro x); auto;
    apply subst_co_erased_tm; auto.
  - apply erased_a_Abs with (L := union L L0). intros. eauto.
    intros. assert (W: x `notin` L0). fsetdec. apply H3 in W.
    inversion W; subst. econstructor; eauto.
    econstructor. eapply Par_fv_preservation in H1; eauto.
  - pick fresh c0.
    destruct_notin.
    move: (e c0 ltac:(auto)) => h0.
    move: (H2 c0 ltac:(auto))  => h1.
    rewrite h0 in h1.
    inversion h1; auto.
  - pick fresh c0.
    destruct_notin.
    move: (e c0 ltac:(auto)) => h0.
    move: (H2 c0 ltac:(auto))  => h1.
    rewrite h0 in h1.
    inversion h1; auto.
  - pick fresh c0.
    destruct_notin.
    move: (e c0 ltac:(auto)) => h0.
    move: (H1 c0 ltac:(auto))  => h1.
    rewrite h0 in h1.
    inversion h1; auto.
Qed.

Lemma Par_erased_tm : forall G D a a', Par G D a a' -> forall (Ea : erased_tm a), erased_tm a'.
Proof.
  apply Par_erased_tm_constraint_mutual.
Qed.

Lemma Par_erased_constraint : forall G D phi phi', ParProp G D phi phi' -> forall (Ephi : erased_constraint phi),  erased_constraint phi'.
Proof.
  apply Par_erased_tm_constraint_mutual.
Qed.

Hint Resolve Par_erased_tm Par_erased_constraint : erased. 

(* ------------------------------------------------------------- *)


Lemma subst1 : forall S D a a' x, Par S D a a' -> 
                             (forall b, erased_tm b ->
                               Par S D (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b)) /\
                             (forall phi, erased_constraint phi ->
                               ParProp S D (tm_subst_tm_constraint a x phi) (tm_subst_tm_constraint a' x phi)).
Proof.
  move => S D a a' x PAR; apply erased_tm_constraint_mutual; intros; simpl; auto.
  all: try destruct rho; try solve [Par_pick_fresh y;
                  autorewrite with subst_open_var; eauto with lc].
  destruct (x0 == x). Unshelve.
  all: eauto.
Qed.

Lemma open1 : forall b S D a a' L, Par S D a a'
  -> (forall x, x `notin` L -> erased_tm (open_tm_wrt_tm b (a_Var_f x)))
  -> Par S D (open_tm_wrt_tm b a) (open_tm_wrt_tm b a').
Proof.
  intros.
  pick fresh x.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ a')] (tm_subst_tm_tm_intro x); auto.
  apply subst1; auto.
Qed.

Lemma open_constraint1 : forall phi S D a a' L, Par S D a a'
  -> (forall x, x `notin` L -> erased_constraint (open_constraint_wrt_tm phi (a_Var_f x)))
  -> ParProp S D (open_constraint_wrt_tm phi a) (open_constraint_wrt_tm phi a').
Proof.
  intros.
  pick fresh x.
  rewrite (tm_subst_tm_constraint_intro x); auto.
  rewrite [(_ _ a')] (tm_subst_tm_constraint_intro x); auto.
  apply subst1; auto.
Qed.

(* Lemma subst2 : forall S D b x, lc_tm b -> *)
(*   forall a a', Par S D a a' -> Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a'). *)

Lemma subst2 : forall b x, lc_tm b ->
  (forall S D a a', Par S D a a' -> Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a')) /\ 
  (forall S D phi phi', ParProp S D phi phi' -> ParProp S D (tm_subst_tm_constraint b x phi) (tm_subst_tm_constraint b x phi')).
Proof.
  intros b x EB.
  apply Par_tm_constraint_mutual; intros; simpl.
  (* intros S D b x EB a a' PAR. *)
  (* induction PAR; simpl. *)
  all: eauto using tm_subst_tm_tm_lc_tm.
  all: autorewrite with subst_open; auto.
  all: try solve [Par_pick_fresh y; autorewrite with subst_open_var; eauto].
  - rewrite tm_subst_tm_tm_fresh_eq.
    eapply Par_Axiom; eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
    move: (Typing_context_fv h0) => ?. split_hyp.
    simpl in *.
    fsetdec.
  - Par_pick_fresh y; eauto.
    have h1: y <> x by auto.
    move: (e y ltac:(auto)) => h0.
    apply (fun_cong (tm_subst_tm_tm b x)) in h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0; auto.
    simpl in h0.
    destruct (@eq_dec tmvar _ y x); subst; try done.
  - Par_pick_fresh y; eauto.
    have h1: y <> x by auto.
    move: (e y ltac:(auto)) => h0.
    apply (fun_cong (tm_subst_tm_tm b x)) in h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h0; auto.
    simpl in h0.
    destruct (@eq_dec tmvar _ y x); subst; try done.
  - Par_pick_fresh y; eauto.
    have h1: y <> x by auto.
    move: (e y ltac:(auto)) => h0.
    apply (fun_cong (tm_subst_tm_tm b x)) in h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_co in h0; auto.
Qed.


Lemma subst3 : forall b b' x,
    (forall S D a a',  Par S D a a' -> Par S D b b' -> erased_tm a ->
    Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a')) /\
    (forall S D phi phi', ParProp S D phi phi' -> Par S D b b' -> erased_constraint phi ->
    ParProp S D (tm_subst_tm_constraint b x phi) (tm_subst_tm_constraint b' x phi')).
Proof.
  intros b b' x.
  apply Par_tm_constraint_mutual; intros; simpl; eauto; erased_inversion; eauto.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - apply subst1; auto.
  - eapply Par_Axiom; eauto.
    rewrite tm_subst_tm_tm_fresh_eq. eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
     move: (Typing_context_fv h0) => ?. split_hyp.
     fsetdec. 
  - move : e => H2.
    pick fresh y.
    move: (H4 y ltac:(auto)) => h0.
    move: (H2 y ltac:(auto)) => h1.
    rewrite h1 in h0. inversion h0. subst.
    eapply (Par_Eta (L \u singleton x)). eauto.
    intros z Fr0.
    move: (H2 z ltac:(auto)) => h2.
    apply (fun_cong (tm_subst_tm_tm b x)) in h2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h2.
    simpl in h2.
    destruct (@eq_dec tmvar _ z x); try done.
    clear Fr. fsetdec.
    eapply Par_lc1. eauto.
  - move : e => H2.
    pick fresh y.
    move: (H4 y ltac:(auto)) => h0.
    move: (H2 y ltac:(auto)) => h1.
    rewrite h1 in h0. inversion h0. subst.
    eapply (Par_EtaIrrel (L \u singleton x)). eauto.
    intros z Fr0.
    move: (H2 z ltac:(auto)) => h2.
    apply (fun_cong (tm_subst_tm_tm b x)) in h2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h2.
    simpl in h2.
    destruct (@eq_dec tmvar _ z x); try done.
    clear Fr. fsetdec.
    eapply Par_lc1. eauto. 
  - move : e => H2.
    pick fresh y.
    move: (H3 y ltac:(auto)) => h0.
    move: (H2 y ltac:(auto)) => h1.
    rewrite h1 in h0. inversion h0. subst.
    eapply (Par_EtaC (L \u singleton x)). eauto.
    intros z Fr0.
    move: (H2 z ltac:(auto)) => h2.
    apply (fun_cong (tm_subst_tm_tm b x)) in h2.
    rewrite tm_subst_tm_tm_open_tm_wrt_co in h2.
    simpl in h2.
    destruct (@eq_dec tmvar _ z x); try done.
    clear Fr.
    eapply Par_lc1. eauto.
  (* ParProp Eq *)
  - inversion H3; eauto.
  (* ParProp Impl *)
  - inversion H2; eauto.
Qed.

Lemma subst3_tm : forall S D b b' x,
    Par S D b b' ->
    forall a a', erased_tm a -> Par S D a a' ->
    Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a').
Proof.
  intros.
  apply subst3; auto.
Qed.

Lemma subst4 : forall b x, lc_co b ->
    (forall S D a a', Par S D a a' ->
    Par S D (co_subst_co_tm b x a) (co_subst_co_tm b x a')) /\
    (forall S D phi phi', ParProp S D phi phi' ->
    ParProp S D (co_subst_co_constraint b x phi) (co_subst_co_constraint b x phi')).
Proof.
  intros b x EB.
  apply Par_tm_constraint_mutual; intros; simpl; auto.
  (* intros S D b x EB a a' PAR. *)
  (* induction PAR; simpl; auto. *)
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - apply Par_Refl. eapply co_subst_co_tm_lc_tm; auto.
  - rewrite co_subst_co_tm_fresh_eq. eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
    move: (Typing_context_fv  h0) => ?. split_hyp.
    simpl in *.
    fsetdec.
  - pick fresh y and apply Par_Eta; eauto.
    move: (e y ltac:(auto)) => h1.
    apply (fun_cong (co_subst_co_tm b x)) in h1.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h1.
    simpl in h1. auto. auto.
  - pick fresh y and apply Par_EtaIrrel; eauto.
    move: (e y ltac:(auto)) => h1.
    apply (fun_cong (co_subst_co_tm b x)) in h1.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h1.
    simpl in h1. auto. auto.
  - pick fresh y and apply Par_EtaC; eauto.
    move: (e y ltac:(auto)) => h1.
    apply (fun_cong (co_subst_co_tm b x)) in h1.
    rewrite co_subst_co_tm_open_tm_wrt_co in h1.
    rewrite co_subst_co_co_var_neq in h1.
    simpl in h1. auto. fsetdec. auto.
Qed.

Lemma multipar_subst3 : forall S D b b' x, erased_tm b ->
    multipar S D b b' ->
    forall a a', erased_tm a -> multipar S D a a' ->
    multipar S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a').
Proof.
    intros S D b b' x ea H.
    dependent induction H; auto; move : H => lca.
  - move => a' a'' ea' H.
    dependent induction H; auto with lngen.
    apply mp_step with (b := (tm_subst_tm_tm a x b)); auto.
    apply subst3; auto. apply IHmultipar.
    eauto with erased.
  - rename a' into a''.
    rename b into a'.
    intros b b'' eb H1.
    dependent induction H1.
    + rename a0 into b.
      apply mp_step with (b := tm_subst_tm_tm a' x b); auto.
      apply subst3; auto. eauto with erased.
    + rename a'0 into b''.
      rename b into b'.
      rename a0 into b.
      apply mp_step with (b := tm_subst_tm_tm a x b'); eauto with erased.
      apply subst3; auto with lc.
Qed.

Lemma multipar_subst4 : forall S D b x, lc_co b ->
    forall a a', multipar S D a a' ->
    multipar S D (co_subst_co_tm b x a) (co_subst_co_tm b x a').
Proof.
  intros S D b x H a a' H0.
  dependent induction H0; eauto with lngen.
  apply mp_step with (b := co_subst_co_tm b x b0); auto.
  apply subst4; auto.
Qed.

Lemma erased_tm_open_tm_wrt_tm: forall a x, erased_tm a -> erased_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros a x H.
  pose K := erased_lc_tm H.
  rewrite open_tm_wrt_tm_lc_tm; eauto.
Qed.

Lemma erased_tm_open_tm_wrt_constraint: forall phi x, erased_constraint phi -> erased_constraint (open_constraint_wrt_tm phi (a_Var_f x)).
Proof.
  intros a x H.
  pose K := erased_lc_constraint H.
  rewrite open_constraint_wrt_tm_lc_constraint; eauto.
Qed.

Hint Resolve erased_tm_open_tm_wrt_tm erased_tm_open_tm_wrt_constraint : erased.


Lemma Par_Pi_exists: ∀ x (G : context) D rho (A B A' B' : tm),
    x `notin` fv_tm_tm_tm B -> Par G D A A'
    → Par G D (open_tm_wrt_tm B (a_Var_f x)) B'
    → Par G D (a_Pi rho A B) (a_Pi rho A' (close_tm_wrt_tm x B')).
Proof.
  intros x G D rho A B A' B' H H0 H1.
  apply (Par_Pi (fv_tm_tm_tm B)); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
  apply subst2; auto.
Qed.

Lemma Par_CPi_exists:  ∀ c (G : context) D (phi phi' : constraint) (a a' : tm),
       c `notin` fv_co_co_tm a -> ParProp G D phi phi'
         → Par G D (open_tm_wrt_co a (g_Var_f c)) (a')
         → Par G D (a_CPi phi a) (a_CPi phi' (close_tm_wrt_co c a')).
Proof.
  intros c G D phi phi' a H H0 H1 H2.
  apply (Par_CPi (singleton c)); auto.
  intros c0 H4.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.

Lemma Par_Abs_exists: ∀ x (G : context) D rho (a a' : tm),
    x `notin` fv_tm_tm_tm a
    → Par G D (open_tm_wrt_tm a (a_Var_f x)) a'
    → Par G D (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')).
Proof.
  intros x G D rho a a' hi0 H0.
  apply (Par_Abs (singleton x)); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x a (a_Var_f x0)); auto.
  apply subst2; auto.
Qed.

Lemma Par_CAbs_exists: forall c (G : context) D (a a': tm),
       c `notin` fv_co_co_tm a
       -> Par G D (open_tm_wrt_co a (g_Var_f c)) a'
       → Par G D (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')).
Proof.
  intros c G D a a' H H0.
  apply (Par_CAbs (singleton c)); auto.
  intros c0 H3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.

Lemma Par_EtaRel_exists : forall (G: context) D a b b' x,
   x `notin` union (fv_tm_tm_tm a) (fv_tm_tm_tm b) ->
   Par G D b b' ->
   (open_tm_wrt_tm a (a_Var_f x)) = a_App b Rel (a_Var_f x) ->
   Par G D (a_UAbs Rel a) b'.
Proof.
  intros G D a b b' x hi0 H0 EQ.
  eapply (Par_Eta (singleton x)); eauto.
  intros x0 h0. apply eta_swap with x; eauto.
Qed.



Lemma Par_EtaRel_close : forall (G: context) D b b' x,
   x `notin` fv_tm_tm_tm b ->
   Par G D b b' ->
   Par G D (a_UAbs Rel (close_tm_wrt_tm x (a_App b Rel (a_Var_f x)))) b'.
Proof.
   intros G D b b' x h0 H. eapply (Par_Eta (singleton x)); eauto.
   intros x0 h1. apply eta_swap with x.
   - rewrite fv_tm_tm_tm_close_tm_wrt_tm. simpl. fsetdec.
   - apply open_tm_wrt_tm_close_tm_wrt_tm.
   Qed.


Lemma Par_open_tm_wrt_co_preservation: forall G D B1 B2 c, Par G D (open_tm_wrt_co B1 (g_Var_f c)) B2 -> exists B', B2 = open_tm_wrt_co B' (g_Var_f c) /\ Par G D (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)).
Proof.
  intros G D B1 B2 c H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma Par_open_tm_wrt_tm_preservation: forall G D B1 B2 x, Par G D (open_tm_wrt_tm B1 (a_Var_f x)) B2 -> exists B', B2 = open_tm_wrt_tm B' (a_Var_f x) /\ Par G D (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros G D B1 B2 x H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_Pi_exists: ∀ x (G : context) D rho (A B A' B' : tm),
       lc_tm (a_Pi rho A B) -> x `notin` fv_tm_tm_tm B -> multipar G D A A'
       → multipar G D (open_tm_wrt_tm B (a_Var_f x)) B'
       → multipar G D (a_Pi rho A B) (a_Pi rho A' (close_tm_wrt_tm x B')).
Proof.
  intros x G D rho A B A' B' lc e H H0.
  dependent induction H; eauto.
  - dependent induction H0; eauto.
      by rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
    apply mp_step with (b := a_Pi rho a (close_tm_wrt_tm x b)); auto.
    + inversion lc; subst; clear lc.
      apply (Par_Pi (singleton x)); auto.
      intros x0 H2.
      rewrite -tm_subst_tm_tm_spec.
      rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
      apply subst2; auto.
    + apply IHmultipar; auto.
      * inversion lc; subst; clear lc.
        constructor; eauto.
        intros x0.
        rewrite -tm_subst_tm_tm_spec.
        apply tm_subst_tm_tm_lc_tm; auto.
        eapply Par_lc2; eauto.
      * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
        fsetdec.
      * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - apply mp_step with (b := a_Pi rho b B); auto.
     + apply (Par_Pi (singleton x)); auto.
       intros x0 H2.
       inversion lc; subst; clear lc; auto.
     + apply IHmultipar; auto.
       inversion lc; subst; clear lc.
       constructor; auto.
       apply Par_lc2 in H; auto.
Qed.

Lemma multipar_Pi_A_proj: ∀ (G : context) D rho (A B A' B' : tm),
    lc_tm A -> multipar G D (a_Pi rho A B) (a_Pi rho A' B')
    -> multipar G D A A'.
Proof.
  intros G D rho A B A' B' h0 h1.
  dependent induction h1; eauto.
  inversion H; subst.
  eapply IHh1; eauto.
  apply mp_step with (b := A'0); auto.
  eapply IHh1; eauto.
  eapply Par_lc2; eauto 1.
Qed.

Lemma multipar_Pi_B_proj: ∀ (G : context) D rho (A B A' B' : tm),
    multipar G D (a_Pi rho A B) (a_Pi rho A' B')
    → (exists L, forall x, x `notin` L -> multipar G D (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x))).
Proof.
  intros G D rho A B A' B' h1.
  dependent induction h1; eauto with lngen.
  Unshelve.
  inversion H; subst.
  eapply IHh1; eauto.
  destruct (IHh1 rho A'0 B'0 A' B') as [L0 h0]; auto.
  exists (L \u L0); eauto.
  apply (fv_tm_tm_tm A').
Qed.


Lemma multipar_CPi_exists:  ∀ c (G : context) D (phi phi' : constraint) (a a' : tm),
       lc_tm (a_CPi phi a) -> c `notin` fv_co_co_tm a -> multipar_prop G D phi phi'
         → multipar G D (open_tm_wrt_co a (g_Var_f c)) a'
         → multipar G D (a_CPi phi a) (a_CPi phi' (close_tm_wrt_co c a')).
Proof.
  intros c G D phi phi' a a' lc e H H0.
  dependent induction H.
  - dependent induction H0.
    + rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
    + apply mp_step with (b := a_CPi phi (close_tm_wrt_co c b)).
      apply Par_CPi_exists with (phi := phi) (phi' := phi) in H1; auto.
      inversion lc; subst.
      move : (H5 c) => h1.
      apply IHmultipar; auto with lngen.
      apply lc_a_CPi_exists with c. assumption.
      rewrite open_tm_wrt_co_close_tm_wrt_co.
      eauto with lc.
      autorewrite with lngen.
      auto.
  - inversion lc; subst.
    apply mp_step with (b := (a_CPi phi2 a)).
    apply Par_CPi with (L := {}); auto.
    apply IHmultipar_prop; auto.
    apply Par_lc2 in H; auto.
Qed.

Lemma multipar_CPi_B_proj:  ∀ (G : context) D (phi phi' : constraint) (a a': tm),
    multipar G D (a_CPi phi a) (a_CPi phi' a')
  → (exists L, forall c, c `notin` L -> multipar G D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c))).
Proof.
  intros G D phi phi' a a' h1.
  dependent induction h1; eauto with lngen.
  Unshelve.
  inversion H; subst.
  eapply IHh1; eauto.
  destruct (IHh1 phi'0 phi' a'0 a') as [L0 h0]; auto.
  exists (L \u L0); eauto.
  apply (fv_tm_tm_constraint phi').
Qed.

Lemma multipar_CPi_phi_proj:  ∀ (G : context) D (phi phi' : constraint) (a a': tm),
    multipar G D (a_CPi phi a) (a_CPi phi' a')
    -> multipar_prop G D phi phi'.
Proof.
  intros G D phi phi' a a' H.
  dependent induction H; eauto.
  inversion H; subst; auto.
  inversion H; subst; eauto.
Qed.

Lemma multipar_Abs_exists: ∀ x (G : context) D rho (a a' : tm),
       lc_tm (a_UAbs rho a) -> x `notin` fv_tm_tm_tm a
       → multipar G D (open_tm_wrt_tm a (a_Var_f x)) a'
       → multipar G D (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')).
Proof.
  intros x G D rho B B' lc e H.
  dependent induction H; eauto 2.
  - autorewrite with lngen. eauto 2.
  - assert (Par G D (a_UAbs rho B) (a_UAbs rho (close_tm_wrt_tm x b))).
    eapply (Par_Abs_exists); auto.
    assert (multipar G D (a_UAbs rho (close_tm_wrt_tm x b))
                       (a_UAbs rho (close_tm_wrt_tm x a'))).
    { apply IHmultipar; auto.
    * inversion lc; subst; clear lc.
        constructor; eauto.
        intros x0.
        rewrite -tm_subst_tm_tm_spec.
        apply tm_subst_tm_tm_lc_tm; auto.
        apply Par_lc2 in H; auto.
    * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
      fsetdec.
    * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto. }
    eapply mp_step; eauto.
Qed.

Lemma multipar_CAbs_exists: forall c (G : context) D (a a': tm),
       lc_tm (a_UCAbs a) -> c `notin` fv_co_co_tm a
       -> multipar G D (open_tm_wrt_co a (g_Var_f c)) a'
       → multipar G D (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')).
Proof.
  intros c G D a a' lc e H.
  dependent induction H; eauto 1.
    by rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  inversion lc; subst.
  apply mp_step with (b:= ( (a_UCAbs (close_tm_wrt_co c b)))); eauto.
  + apply (Par_CAbs (singleton c)); auto.
    intros c1 h0.
    rewrite -co_subst_co_tm_spec.
    rewrite (co_subst_co_tm_intro c a (g_Var_f c1)); auto.
    apply subst4; auto.
  + apply IHmultipar; eauto.
    * constructor; eauto 1.
      intros c1.
      rewrite -co_subst_co_tm_spec.
      apply co_subst_co_tm_lc_tm; auto.
      apply Par_lc2 in H; auto.
    * rewrite fv_co_co_tm_close_tm_wrt_co_rec.
      fsetdec.
    * rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
Qed.

Lemma multipar_open_tm_wrt_co_preservation: forall G D B1 B2 c, multipar G D (open_tm_wrt_co B1 (g_Var_f c)) B2 -> exists B', B2 = open_tm_wrt_co B' (g_Var_f c) /\ multipar G D (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)).
Proof.
  intros G D B1 B2 c H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_open_tm_wrt_tm_preservation: forall G D B1 B2 x, multipar G D (open_tm_wrt_tm B1 (a_Var_f x)) B2 -> exists B', B2 = open_tm_wrt_tm B' (a_Var_f x) /\ multipar G D (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros G D B1 B2 x H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma context_Par_irrelevance: (forall G1 D1 a a',
                                             Par G1 D1 a a' -> forall G2 D2, Par G2 D2 a a') /\
                               (forall G1 D1 phi phi',
                                             ParProp G1 D1 phi phi' -> forall G2 D2, ParProp G2 D2 phi phi').
Proof.
  apply Par_tm_constraint_mutual; intros; eauto.
Qed.


Lemma multipar_context_independent: forall G1 G2 D A B,  multipar G1 D A B -> multipar G2 D A B.
Proof.
  induction 1; eauto.
  eapply context_Par_irrelevance in H; eauto.
Qed.


Lemma multipar_prop_context_independent: forall G1 G2 D phi1 phi2,  multipar_prop G1 D phi1 phi2 -> multipar_prop G2 D phi1 phi2.
Proof.
  induction 1; eauto.
  eapply context_Par_irrelevance in H; eauto.
Qed.


(* -------------------- weakening stuff for Par ---------------------- *)

Lemma Par_weaken_available :
  (forall G D a b, Par G D a b -> forall D', D [<=] D' -> Par G D' a b) /\
  (forall G D phi1 phi2, ParProp G D phi1 phi2 -> forall D', D [<=] D' -> ParProp G D' phi1 phi2).
Proof.
  apply Par_tm_constraint_mutual; eauto.
Qed.

Lemma Par_respects_atoms:
  (forall G D a b, Par G D a b -> forall D', D [=] D' -> Par G D' a b) /\
  (forall G D phi phi', ParProp G D phi phi' -> forall D', D [=] D' -> ParProp G D' phi phi').
Proof.
  apply Par_tm_constraint_mutual; eauto.
Qed.

Lemma Par_availability_independence: forall G D1 D2 a b, Par G D1 a b -> Par G D2 a b.
Proof.
  intros. eapply context_Par_irrelevance; eauto.
Qed.


Lemma Par_remove_available:
  (forall G D a b, Par G D a b -> Par G (AtomSetImpl.inter D (dom G)) a b) /\
  (forall G D phi phi', ParProp G D phi phi' -> ParProp G (AtomSetImpl.inter D (dom G)) phi phi').
Proof.
  apply Par_tm_constraint_mutual; eauto.
Qed.

Lemma Par_weakening :
  (forall G0 D a b, Par G0 D a b ->
              forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) ->  Par (F ++ E ++ G) D a b) /\
  (forall G0 D phi phi', ParProp G0 D phi phi' ->
              forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) ->  ParProp (F ++ E ++ G) D phi phi').
Proof.
  apply Par_tm_constraint_mutual; eauto.
Qed.

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

Inductive multipar S D ( a : tm) : tm -> Prop :=
| mp_refl : multipar S D a a
| mp_step : forall b c, Par S D a b -> multipar S D b c -> multipar S D a c.

Hint Constructors multipar.


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
  | [H : erased_tm (a_Case _ _) |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_brs (br_One _ _ _ ) |- _ ] =>
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


Lemma erased_tm_erase_mutual :
  (forall a, lc_tm a -> erased_tm (erase a))
  /\ (forall a, lc_brs a -> erased_brs (erase a))
  /\ (forall a, lc_co a -> True)
  /\ (forall phi, lc_constraint phi -> forall a b A, phi = (Eq a b A) ->
                                         erased_tm (erase a) /\ erased_tm (erase b)
                                         /\ erased_tm (erase A)).

Proof.
  apply lc_tm_lc_brs_lc_co_lc_constraint_mutind; intros; simpl; eauto.
  all: try solve [ try (destruct rho); simpl; eauto].
  all: try solve [erased_case].

  - destruct phi. destruct (H _ _ _ eq_refl) as (h0 & h1 & h2). simpl.
    erased_case.
  - invert_syntactic_equality. auto.
Qed.

Lemma erased_tm_erase : forall a, lc_tm a -> erased_tm (erase a).
Proof.
  intros.
  destruct erased_tm_erase_mutual.
  eauto.
Qed.

Hint Resolve erased_tm_erase : erased.


Inductive erased_sort : sort -> Prop :=
| erased_Tm : forall a, erased_tm a -> erased_sort (Tm a)
| erased_Co : forall a b A, erased_tm a -> erased_tm b -> erased_tm A -> erased_sort (Co (Eq a b A)).

Definition erased_context : context -> Prop :=
  Forall (fun p => match p with (a,s) => erased_sort s end).

Definition joins S D a b := exists c, erased_context S /\ erased_tm a /\ erased_tm b /\
                               multipar S D a c /\ multipar S D b c.


Lemma erased_lc_mutual : (forall a, erased_tm a -> lc_tm a) /\ (forall a, erased_brs a -> lc_brs a).
  eapply erased_tm_erased_brs_mutual; intros; auto.
Qed.

Lemma erased_lc : forall a, erased_tm a -> lc_tm a.
  eapply erased_lc_mutual.
Qed.

Hint Resolve erased_lc : lc.

Lemma subst_tm_erased_mutual : forall x b, erased_tm b ->
  (forall a , erased_tm  a -> erased_tm  (tm_subst_tm_tm b x a)) /\
  (forall a , erased_brs a -> erased_brs (tm_subst_tm_brs b x a)).
Proof.
  intros x b Eb. eapply erased_tm_erased_brs_mutual; intros; simpl; eauto 2.
  all: try solve [erased_pick_fresh x0; autorewrite with subst_open_var; eauto using erased_lc].
  destruct eq_dec; eauto.
Qed.

Lemma subst_tm_erased :  forall x b, erased_tm b ->
  (forall a , erased_tm  a -> erased_tm  (tm_subst_tm_tm b x a)).
Proof.
  intros x b H. eapply subst_tm_erased_mutual. auto.
Qed.


Lemma subst_co_erased_mutual : forall c g, lc_co g ->
   (forall a, erased_tm  a -> erased_tm  (co_subst_co_tm g c a)) /\
   (forall a, erased_brs a -> erased_brs (co_subst_co_brs g c a)).
Proof.
  intros x b Eb. eapply erased_tm_erased_brs_mutual; intros; simpl; eauto 2.
  all: try solve [erased_pick_fresh x0; autorewrite with subst_open_var; eauto using erased_lc].
Qed.

Lemma subst_co_erased : forall c g a , lc_co g -> erased_tm a -> erased_tm (co_subst_co_tm g c a).
Proof.
  intros c g a H. eapply subst_co_erased_mutual. auto.
Qed.


Hint Resolve subst_tm_erased subst_co_erased : erased.

(*

Fixpoint append_brs (b1 : brs) (b2 : brs) : brs :=
  match b1 with
  | br_None => b2
  | br_One K a b1' => br_One K a (append_brs b1' b2)
  end.

Lemma append_brs_br_None : forall b, append_brs b br_None = b.
induction b; simpl; auto.
rewrite IHb.  auto.
Qed.

Lemma in_append : forall b1 b2 x a, in_brs x a b2 -> in_brs x a (append_brs b1 b2).
Proof.
  induction b1.
  intros. simpl. auto.
  intros. simpl. econstructor; eauto.
Qed.

(* A tactic for proofs about brs. *)
Ltac brs_induction b :=
  rewrite- {1}[b] append_brs_br_None;
  generalize br_None;
  induction b as [|K a b Ihb b0 H];
  intros; eauto;
  simpl in H;
  move: (H K a (in_brshere K a (append_brs b b0) I I));
  move: (Ihb b0 (fun K0 a0 H0 => H K0 a0 (in_brsthere K0 a0 K a (append_brs b b0) I H0))).

Lemma in_brs_lc : forall b, (forall K a, in_brs K a b -> lc_tm a) -> lc_brs b.
Proof.
  move => b;
  brs_induction b => h1 h2.
  auto.
Qed.

Lemma dom_in_brs :
  forall a K b1, in_brs K a b1 ->  forall b2, dom_br b1 = dom_br b2 -> exists a0, in_brs K a0 b2.
Proof.
  intros.
  dependent induction H; destruct b2; inversion H1.
  exists a0. auto.
  destruct (IHin_brs b2 H4) as [a0' IN].
  exists a0'. eauto.
Qed.

Check sym_eq.
Check eq_sym.

Ltac apply_dom_in_brs :=
  match goal with [H3 : in_brs _ _ ?b , H0 : dom_br ?b = dom_br _ |- _ ] =>
                  move: (dom_in_brs H3 _ H0)
 | [H3 : in_brs _ _ ?b , H0 : dom_br _ = dom_br ?b |- _ ] =>
                  move: (dom_in_brs H3 _ (eq_sym H0))
  end.

Lemma in_brs_erased : forall b, (forall K a, in_brs K a b -> erased_tm a) -> erased_brs b.
Proof.
  move => b;
  brs_induction b => h1 h2.
  auto.
Qed.

Ltac induction_in_brs P :=
  induction P;
  intros;
   match goal with
   | [H : in_brs _ _ br_None |- _ ] => inversion H
   | [H : in_brs _ _ (br_One _ _ _) |- _ ] => inversion H; subst; eauto
  end.


Lemma erased_in_brs : forall b, erased_brs b -> (forall K a, in_brs K a b -> erased_tm a).
Proof. move => b P; induction_in_brs P.
Qed.

*)


(* FIXME: find a good place for this tactic. *)
(* cannot move this to ett_ind.v because need Toplevel_lc ??? *)
Ltac lc_toplevel_inversion :=
  match goal with
  | [ b : binds ?F _ toplevel |- _ ] =>
    apply Toplevel_lc in b; inversion b; auto
end.


Lemma Par_lc1_mutual :  (forall G D a a' , Par G D a a' -> lc_tm a) /\
(forall G D br br', Par_brs G D br br' -> lc_brs br).
Proof.
  apply Par_tm_Par_brs_mutual; auto.
  intros.
  apply_lc_exists x; unfold not in *; rewrite_body.
Qed.

Lemma Par_lc1 : forall G D a a' , Par G D a a' -> lc_tm a.
  apply Par_lc1_mutual.
Qed.


Lemma Par_lc2_mutual :  (forall G D a a' , Par G D a a' -> lc_tm a') /\
(forall G D br br', Par_brs G D br br' -> lc_brs br').
Proof.
  apply Par_tm_Par_brs_mutual; intros; auto.
  - lc_solve.
  - lc_solve.
  - lc_toplevel_inversion.
Qed.

Lemma Par_lc2 : forall G D a a' , Par G D a a' -> lc_tm a'.
Proof. apply Par_lc2_mutual. Qed.


Hint Resolve Par_lc1 Par_lc2 : lc.

Lemma typing_erased_mutual:
    (forall G b A, Typing G b A -> erased_tm b) /\
    (forall G0 phi (H : PropWff G0 phi),
        forall A B T, phi = Eq A B T -> erased_tm A /\ erased_tm B /\ erased_tm T) /\
     (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\
     (forall G0 D A B T (H : DefEq G0 D A B T), True) /\
     (forall G0 (H : Ctx G0), True).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  all : try solve [inversion H2; subst; auto].
  all : try solve [econstructor; eauto].
  - destruct phi.
    apply (@erased_a_CPi L); try solve [apply (H0 a b A); auto]; auto.
Qed.


Lemma Typing_erased: forall G b A, Typing G b A -> erased_tm b.
Proof.
  apply typing_erased_mutual.
Qed.

Hint Resolve Typing_erased : erased.

Lemma typing_erased_type_mutual:
    (forall G b A, Typing G b A -> erased_tm A) /\
    (forall G0 phi (H : PropWff G0 phi), True) /\
     (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\
     (forall G0 D A B T (H : DefEq G0 D A B T), True) /\
     (forall G0 (H : Ctx G0), erased_context G0).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  all: unfold erased_context in *.
  all: eauto using Typing_erased.
    all: try solve [inversion H; pick fresh x;
      rewrite (tm_subst_tm_tm_intro x); auto;
        eapply subst_tm_erased;
        eauto using Typing_erased].
  - eapply Forall_forall in H; eauto. simpl in H. inversion H. auto.
  - inversion p. econstructor; eauto using Typing_erased.
  - inversion H; pick fresh x;
      rewrite (co_subst_co_tm_intro x); auto.
        eapply subst_co_erased;
        eauto using Typing_erased.
  - apply Forall_forall.
    intros s h0. destruct s.
    destruct h0. inversion H1. econstructor.
    eauto using Typing_erased.
    eapply Forall_forall in H; eauto. simpl in H. auto.
  - apply Forall_forall.
    intros s h0. destruct s. inversion p. subst.
    destruct h0. inversion H4. econstructor;  eauto using Typing_erased.
    eapply Forall_forall in H; eauto. simpl in H. auto.
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
      [ H4 : ∀ x : atom, x `notin` ?L0 → erased_tm (open_tm_wrt_tm ?a (a_Var_f x))
                         |- _ ] =>
      move: (H4 x ltac:(auto)) => Ea; clear H4
    end.

(* Move this to ett_ind? *)
Ltac eta_eq y EQ :=
   match goal with
      [ H :
          ∀ x : atom,
            x `notin` ?L → open_tm_wrt_tm ?a (a_Var_f x) =
                           a_App ?b ?rho _ |- _ ] =>
   move: (H y ltac:(auto)) =>  EQ
end.

Lemma Par_erased_tm_mutual :
  (forall G D a a', Par G D a a' -> erased_tm a -> erased_tm a') /\
  (forall G D a a', Par_brs G D a a' -> erased_brs a -> erased_brs a').
Proof.
  eapply Par_tm_Par_brs_mutual; eauto; intros; erased_inversion; eauto 2.
  all: try solve [ erased_pick_fresh x; auto ].
  all: eauto.
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (tm_subst_tm_tm_intro x); auto;
    apply subst_tm_erased; auto.
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (co_subst_co_tm_intro x); auto;
    apply subst_co_erased; auto.
  - eauto with erased.
  - (* Eta *)
    eapply H; auto.
    pick fresh x;
    erased_body x Eaa;
    eta_eq x E.
    rewrite E in Eaa; inversion Eaa; auto.
Qed.

Lemma Par_erased_tm : forall G D a a', Par G D a a' -> erased_tm a -> erased_tm a'.
Proof. apply Par_erased_tm_mutual. Qed.

Hint Resolve Par_erased_tm : erased.

(* ------------------------------------------------------------- *)


Lemma subst1_mutual : forall x S D a a', Par S D a a' ->
  (forall b, erased_tm b    -> Par S D (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b)) /\
  (forall br, erased_brs br -> Par_brs S D (tm_subst_tm_brs a x br) (tm_subst_tm_brs a' x br)).
Proof.
  intros x S D a a' PAR.
  apply erased_tm_erased_brs_mutual; intros; simpl; auto.
  all: try destruct (x0 == x); auto.
  all: try solve [Par_pick_fresh y;
                  autorewrite with subst_open_var; eauto 3 with lc].
  Unshelve.
  all: eauto.
Qed.

Lemma subst1 : forall b S D a a' x, Par S D a a' -> erased_tm b ->
                               Par S D (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b).
Proof.
intros. eapply subst1_mutual; eauto. Qed.


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


Lemma subst2_mutual : forall b x, lc_tm b ->
  (forall S D a a', Par S D a a' -> Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a')) /\
  (forall S D a a', Par_brs S D a a' -> Par_brs S D (tm_subst_tm_brs b x a) (tm_subst_tm_brs b x a')).
Proof.
  intros b x EB.
  eapply Par_tm_Par_brs_mutual; simpl; intros.
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
Qed.

Lemma subst2 : forall S D b x, lc_tm b ->
  forall a a', Par S D a a' -> Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a').
Proof. intros. eapply subst2_mutual; eauto. Qed.

Lemma subst3_mutual : forall b b' x,
    (forall S D a a', Par S D a a' -> Par S D b b' -> erased_tm a ->
             Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a')) /\
    (forall S D a a', Par_brs S D a a' -> Par S D b b' -> erased_brs a ->
             Par_brs S D (tm_subst_tm_brs b x a) (tm_subst_tm_brs b' x a')).
Proof.
  intros b b' x.
  apply Par_tm_Par_brs_mutual; intros; simpl; eauto 2; erased_inversion; eauto 4.
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
  - pick fresh y.

    match goal with [H4 : forall x, x `notin` L0 -> _ |- _ ] =>
                    move: (H4 y ltac:(auto)) => h0 end.
    match goal with [H2 : forall x, x `notin` L -> _ |- _ ] =>
                    move: (H2 y ltac:(auto)) => h1 end.
    rewrite h1 in h0. inversion h0. subst.
    eapply (Par_Eta (L \u singleton x)). eauto.
    intros z Fr0.
    match goal with [H2 : forall x, x `notin` L -> _ |- _ ] =>
                    move: (H2 z ltac:(auto)) => h2 end.
    apply (fun_cong (tm_subst_tm_tm b x)) in h2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h2.
    simpl in h2.
    destruct (@eq_dec tmvar _ z x); try done.
    clear Fr. fsetdec.
    eapply Par_lc1. eauto.
    Unshelve. all: eauto.
Qed.

Lemma subst3 : forall S D b b' x,
    Par S D b b' ->
    forall a a', erased_tm a -> Par S D a a' ->
    Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a').
Proof.
  intros. apply subst3_mutual; eauto.
Qed.


Lemma subst4_mutual : forall b x, lc_co b ->
    (forall S D a a', Par S D a a' ->
    Par S D (co_subst_co_tm b x a) (co_subst_co_tm b x a')) /\
    (forall S D a a', Par_brs S D a a' ->
    Par_brs S D (co_subst_co_brs b x a) (co_subst_co_brs b x a')).

Proof.
  intros b x EB.
  apply Par_tm_Par_brs_mutual; intros; simpl; auto.
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
  -
    pick fresh y and apply Par_Eta; eauto.
    match goal with [H : forall x, x `notin` L -> _ |- _ ] =>
                    move: (H y ltac:(auto)) => h1 end.
    apply (fun_cong (co_subst_co_tm b x)) in h1.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h1.
    simpl in h1. auto. auto.
Qed.

Lemma subst4 : forall S D b x, lc_co b ->
    forall a a', Par S D a a' ->
    Par S D (co_subst_co_tm b x a) (co_subst_co_tm b x a').
Proof.
  intros. apply subst4_mutual; eauto.
Qed.


Lemma multipar_subst3 : forall S D b b' x, erased_tm b ->
    multipar S D b b' ->
    forall a a', erased_tm a -> multipar S D a a' ->
    multipar S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a').
Proof.
  intros S D b b' x lc H.
  dependent induction H; auto.
  - intros a0 a' lc2 H.
    dependent induction H; auto.
    apply (@mp_step _ _ _ ((tm_subst_tm_tm a x b))); auto.
    apply subst3; auto.
    apply Par_Refl; eapply erased_lc; eauto.
    apply IHmultipar.
    eapply Par_erased_tm; eauto.
  - intros a0 a' lc2 H1.
    dependent induction H1; auto.
    apply (@mp_step _ _ _ (tm_subst_tm_tm b x a0)); auto.
    apply subst3; auto.
    apply Par_Refl; eapply erased_lc; eauto.
    apply IHmultipar; auto.
    eapply Par_erased_tm; eauto.
    apply (@mp_step _ _ _ ((tm_subst_tm_tm a x b0))); auto.
    apply subst2; auto.
    eapply Par_lc1; eauto.
    apply IHmultipar0; auto.
    eapply Par_erased_tm; eauto.
Qed.

Lemma multipar_subst4 : forall S D b x, lc_co b ->
    forall a a', multipar S D a a' ->
    multipar S D (co_subst_co_tm b x a) (co_subst_co_tm b x a').
Proof.
  intros S D b x H a a' H0.
  dependent induction H0; eauto.
  apply (@mp_step _ _ _ (co_subst_co_tm b x b0)); auto.
  apply subst4; auto.
Qed.

Lemma erased_tm_open_tm_wrt_tm: forall a x, erased_tm a -> erased_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros a x H.
  pose K := erased_lc H.
  rewrite open_tm_wrt_tm_lc_tm; eauto.
Qed.

Hint Resolve erased_tm_open_tm_wrt_tm : erased.


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

Lemma Par_CPi_exists:  ∀ c (G : context) D (A B a A' B' a' T T': tm),
       c `notin` fv_co_co_tm a -> Par G D A A'
       → Par G D B B' -> Par G D T T'
         → Par G D (open_tm_wrt_co a (g_Var_f c)) (a')
         → Par G D (a_CPi (Eq A B T) a) (a_CPi (Eq A' B' T') (close_tm_wrt_co c a')).
Proof.
  intros c G D A B a A' B' a' T T' H H0 H1 h0 H2.
  apply (Par_CPi (singleton c)); auto.
  intros c0 H3.
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
    apply (@mp_step _ _ _ (a_Pi rho a (close_tm_wrt_tm x b))); auto.
    + inversion lc; subst; clear lc.
      apply (Par_Pi (singleton x)); auto.
      intros x0 H1.
      rewrite -tm_subst_tm_tm_spec.
      rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
      apply subst2; auto.
    + apply IHmultipar; auto.
      * inversion lc; subst; clear lc.
        constructor; eauto.
        intros x0.
        rewrite -tm_subst_tm_tm_spec.
        apply tm_subst_tm_tm_lc_tm; auto.
        apply Par_lc2 in H; auto.
      * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
        fsetdec.
      * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - apply (@mp_step _ _ _ (a_Pi rho b B)); auto.
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
  apply (@mp_step _ _ _ A'0); auto.
  eapply IHh1; eauto.
  eapply Par_lc2; eauto 1.
Qed.

Lemma multipar_Pi_B_proj: ∀ (G : context) D rho (A B A' B' : tm),
    multipar G D (a_Pi rho A B) (a_Pi rho A' B')
    → (exists L, forall x, x `notin` L -> multipar G D (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x))).
Proof.
  intros G D rho A B A' B' h1.
  dependent induction h1; eauto.
  Unshelve.
  inversion H; subst.
  eapply IHh1; eauto.
  destruct (IHh1 rho A'0 B'0 A' B') as [L0 h0]; auto.
  exists (L \u L0); eauto.
  apply (fv_tm_tm_tm A').
Qed.


Lemma multipar_CPi_exists:  ∀ c (G : context) D (A B a T A' B' a' T': tm),
       lc_tm (a_CPi (Eq A B T) a) -> c `notin` fv_co_co_tm a -> multipar G D A A'
       → multipar G D B B' -> multipar G D T T'
         → multipar G D (open_tm_wrt_co a (g_Var_f c)) a'
         → multipar G D (a_CPi (Eq A B T) a) (a_CPi (Eq A' B' T') (close_tm_wrt_co c a')).
Proof.
  intros c G D A B a T A' B' a' T' lc e H H0 H2 H1.
  dependent induction H; eauto 1.
  - dependent induction H0; eauto 1.
    + dependent induction H1; eauto 1.
      * dependent induction H2; eauto 1.
        rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
        inversion lc; subst.
        inversion H3; subst.
        apply mp_step with (b:= (a_CPi (Eq a0 a1 b) a)); eauto.
        apply IHmultipar; auto.
        apply (lc_a_CPi_exists c); auto.
        constructor; eauto.
        eapply Par_lc2; eauto.
      * eapply mp_step with (b:= (a_CPi (Eq a0 a1 T) (close_tm_wrt_co c b))); eauto.
        -- inversion lc; subst; clear lc.
           inversion H4; subst; clear H4.
           apply (Par_CPi (singleton c)); auto.
           intros c1 H0.
           rewrite -co_subst_co_tm_spec.
           rewrite (co_subst_co_tm_intro c a (g_Var_f c1)); auto.
           apply subst4; auto.
        -- apply IHmultipar; eauto.
           ++ inversion lc; subst; clear lc.
              constructor; eauto 1.
              intros c1.
              rewrite -co_subst_co_tm_spec.
              apply co_subst_co_tm_lc_tm; auto.
              apply Par_lc2 in H; auto.
           ++ rewrite fv_co_co_tm_close_tm_wrt_co_rec.
              fsetdec.
           ++ rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
      + eapply mp_step with (b:= (a_CPi (Eq a0 b T) a)); eauto.
        -- inversion lc; subst; clear lc.
           inversion H5; subst; clear H5.
           apply (Par_CPi (singleton c)); auto.
        -- apply IHmultipar; eauto.
           inversion lc; subst.
           apply lc_a_CPi; eauto.
           inversion H5; subst.
           constructor; eauto.
           eapply Par_lc2; eauto.
  - apply mp_step with (b:= (a_CPi (Eq b B T) a)); auto.
    inversion lc; subst.
    inversion H6; subst.
      by apply (Par_CPi (singleton c)); auto.
     apply IHmultipar; auto.
     inversion lc; subst; clear lc.
     constructor; auto.
     constructor; auto.
     apply Par_lc2 in H; auto.
     inversion H6; auto.
     inversion H6; auto.
     Unshelve. apply (fv_co_co_tm a).
Qed.

Lemma multipar_CPi_B_proj:  ∀ (G : context) D (A B a A' B' a' T T': tm),
    multipar G D (a_CPi (Eq A B T) a) (a_CPi (Eq A' B' T') a')
  → (exists L, forall c, c `notin` L -> multipar G D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c))).
Proof.
  intros G D A B a A' B' a' T T' h1.
  dependent induction h1; eauto.
  Unshelve.
  inversion H; subst.
  eapply IHh1; eauto.
  destruct (IHh1 A'0 B'0 a'0 A' B' a' A1' T') as [L0 h0]; auto.
  exists (L \u L0); eauto.
  apply (fv_tm_tm_tm A').
Qed.

Lemma multipar_CPi_phi_proj:  ∀ (G : context) D (A B a A' B' a' T T': tm),
    multipar G D (a_CPi (Eq A B T) a) (a_CPi (Eq A' B' T') a')
    -> (multipar G D A A'/\ multipar G D B B' /\ multipar G D T T').
Proof.
  intros G D A B a A' B' a' T T' H.
  dependent induction H; eauto.
  inversion H; subst.
  eapply IHmultipar; eauto.
  repeat split; eauto.
  apply mp_step with (b := A'0); auto.
  destruct (IHmultipar A'0 B'0 a'0 A' B' a' A1' T'); auto.
  destruct (IHmultipar A'0 B'0 a'0 A' B' a' A1' T'); auto.
  apply mp_step with (b:= B'0); auto.
  apply H2.
  destruct (IHmultipar A'0 B'0 a'0 A' B' a' A1' T'); auto.
  apply mp_step with (b:= A1'); auto.
  apply H2.
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
                       (a_UAbs rho (close_tm_wrt_tm x c))).
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


Lemma context_Par_irrelevance_mutual:
  (forall G1 D1 a a',
      Par G1 D1 a a' -> forall G2 D2, Par G2 D2 a a' ) /\
  (forall G1 D1 a a',
      Par_brs G1 D1 a a' -> forall G2 D2, Par_brs G2 D2 a a').
Proof.
  eapply Par_tm_Par_brs_mutual;intros; eauto.
Qed.
Lemma context_Par_irrelevance: forall G1 G2 D1 D2 a a',
                                             Par G1 D1 a a' -> Par G2 D2 a a'.
Proof.
  intros; eapply context_Par_irrelevance_mutual; eauto.
Qed.


Lemma multipar_context_independent: forall G1 G2 D A B,  multipar G1 D A B -> multipar G2 D A B.
Proof.
  induction 1; eauto.
  apply (@context_Par_irrelevance _ G2 D D) in H; eauto.
Qed.


(* -------------------- weakening stuff for Par ---------------------- *)

Lemma Par_weaken_available_mutual :
  (forall G D a b, Par G D a b -> forall D', D [<=] D' -> Par G D' a b) /\
  (forall G D a b, Par_brs G D a b -> forall D', D [<=] D' -> Par_brs G D' a b).
Proof.
  eapply Par_tm_Par_brs_mutual;intros; eauto 4; try done.
  - econstructor; eauto 2.
Qed.

Lemma Par_weaken_available :
  forall G D a b, Par G D a b -> forall D', D [<=] D' -> Par G D' a b.
Proof.
  intros. eapply Par_weaken_available_mutual; eauto.
Qed.

(*
These are unused in the rest of the development, so I haven't updated them to include
Par_brs.

Lemma Par_availability_independence: forall G D1 D2 a b, Par G D1 a b -> Par G D2 a b.
Proof.
  induction 1; eauto.
Qed.


Lemma Par_remove_available:
  forall G D a b, Par G D a b -> Par G (AtomSetImpl.inter D (dom G)) a b.
Proof.
  induction 1; eauto 4; try done.
Qed.

Lemma Par_weakening :
  forall G0 D a b, Par G0 D a b ->
  forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) ->  Par (F ++ E ++ G) D a b.
Proof.
  intros; induction H; pre; subst; try done; eauto 4.
  all: first [Par_pick_fresh c;
       try auto_rew_env; apply_first_hyp; try simpl_env | idtac]; eauto 3.
Qed.
*)
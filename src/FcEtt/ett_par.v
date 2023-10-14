Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.grade_subst.


Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Import ext_wf.

Require Export FcEtt.ext_erased.


Require Import FcEtt.erase_syntax.

Require Export FcEtt.toplevel.

Require Export FcEtt.ett_value.

Require Import Metalib.CoqEqDec.


(* ------------------------------------------ *)

(* Synatactic properties about parallel reduction. (Excluding confluence.) *)

(* ------------------------------------------ *)


(* TODO: move these definitions to the OTT file. *)

(* Hint Constructors multipar. *)

Hint Constructors multipar : core.
Hint Constructors multipar_prop : core.

(* NOTE: we have a database 'erased' for proving that terms are erased. *)

(* Tactics concerning erased terms. *)

Definition joins P psi a b := exists c, uniq P /\ erased_tm a /\ erased_tm b /\
                               multipar P psi a c /\ multipar P psi b c.

Definition joins_constraint P psi phi1 phi2 := exists phi3, uniq P  /\
                                                     erased_constraint phi1 /\
                                                     erased_constraint phi2 /\
                                                     multipar_prop P psi phi1 phi3 /\ multipar_prop P psi phi2 phi3.


Ltac invert_CGrade a :=
  match goal with 
    [ H : CGrade ?P ?phi ?psi a |- _] => inversion H ; subst 
  end.

(* erased_tm t -> x notin open_co_tm t (g_Var x)  *)
Lemma Grade_substitution_co_CGrade : forall P2 c phi P1 psi b,
      Grade (P2 ++ c ~ (phi, e_Co) ++ P1) psi b
    -> Grade (P2 ++ P1) psi (co_subst_co_tm g_Triv c b).
Proof.
  sfirstorder use:CGrade_Grade_substitution_triv_CGrade.
Qed.

Lemma Grade_substitution_co_same : forall P2 c phi P1 psi b,
      Grade (P2 ++ c ~ (phi, e_Co) ++ P1) psi b
    -> Grade (P2 ++ P1) psi (co_subst_co_tm g_Triv c b).
Proof.
  sfirstorder use:Grade_substitution_co_CGrade.
Qed.

Lemma Grade_open_co : forall P psi c psi0 a,
  c `notin` fv_co_co_tm a ->
  Grade ([(c, (psi0, e_Co))] ++ P) psi (open_tm_wrt_co a (g_Var_f c)) ->
  Grade P psi (open_tm_wrt_co a g_Triv).
Proof.
  intros.
  move: (Grade_substitution_co_same nil c psi0 P H0) => ss.
  rewrite co_subst_co_tm_open_tm_wrt_co in ss;
    eauto using Grade_lc.
  rewrite co_subst_co_co_var in ss.
  rewrite co_subst_co_tm_fresh_eq in ss; auto.
Qed.

Lemma Par_grade_mutual :
  (  forall P1 psi a b, Par P1 psi a b -> Grade P1 psi a /\ Grade P1 psi b) /\
  (  forall P1 psi phi1 phi2, ParProp P1 psi phi1 phi2 -> CoGrade P1 psi phi1 /\ CoGrade P1 psi phi2) /\
  (  forall P1 psi psi0 a b, CPar P1 psi psi0 a b -> CGrade P1 psi psi0 a /\ CGrade P1 psi psi0 b) /\
  (  forall P1 psi psi0 phi1 phi2, CParProp P1 psi psi0 phi1 phi2 -> True).
Proof.
  apply Par_tm_constraint_mutual.
  all: split; split_hyp; eauto.
  all: try solve [invert_Grade; subst; auto].
  all: try solve [fresh_apply_Grade x; auto; repeat spec x; split_hyp; eauto].
  - invert_Grade; subst. pick fresh y; repeat spec y.
    invert_CGrade b'. eapply Grade_open_tm; eauto. eapply Grade_open_tm_irrel; eauto. 
  - invert_Grade; subst. pick fresh y; repeat spec y.
    eapply Grade_open_co; eauto.
  (* well-gradedness of toplevel *)
  - econstructor; eauto.
    apply toplevel_closed in b.
admit.
  - admit.                      (* check the proof for subst tm : this should done in a similar fashion *)
  - have h0 : ECtx P by sfirstorder use:Grade_ECtx_mutual.
    fresh_apply_Grade x; auto; repeat spec x; split_hyp; eauto. rewrite e.
    pose proof Grade_uniq H.
    constructor.
    + qauto l: on use: Grade_uniq, Grade_weakening ctrs: uniq, Grade.
    + destruct (q_leb psi0 psi) eqn:eq.
      * apply CG_Leq. sfirstorder ctrs:Grade.
        econstructor; eauto.
      * apply CG_Nleq; eauto.
  - fresh_apply_Grade x; auto; repeat spec x; split_hyp; eauto. rewrite e.
    pose proof Grade_uniq H.
    constructor.
    qauto l: on use: Grade_uniq, Grade_weakening ctrs: uniq, Grade.
Admitted.  


Lemma ParProp_refl : forall P, ECtx P -> forall psi phi, CoGrade P psi phi -> ParProp P psi phi phi.
Proof.
  move => P HCtx psi phi.
  elim => /ltac:(sfirstorder depth:1).
Qed.

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


(* YL: This is no longer true because of the CPar rule *)
(* do we need to define an alternative version of fv_tm_tm_tm with grades? *)
(* Lemma Par_fv_preservation: forall x,  *)
(*   (forall P1 psi a b, Par P1 psi a b -> *)
(*              x `notin` fv_tm_tm_tm a -> *)
(*              x `notin` fv_tm_tm_tm b) /\ *)
(*   (forall P1 psi phi1 phi2, ParProp P1 psi phi1 phi2 -> *)
(*              x `notin` fv_tm_tm_constraint phi1 -> *)
(*              x `notin` fv_tm_tm_constraint phi2) /\ *)
(*   (forall P1 psi psi0 a b, CPar P1 psi psi0 a b -> x `notin` fv_tm_tm_tm a -> x `notin` fv_tm_tm_tm b) /\ *)
(*   (forall P1 psi psi0 phi1 phi2, CParProp P1 psi psi0 phi1 phi2 -> *)
(*             x `notin` fv_tm_tm_constraint phi1 -> x `notin` fv_tm_tm_constraint phi2). *)
(* Proof. *)
(*   move => x. *)
(*   apply Par_tm_constraint_mutual; intros; eauto 2; simpl in *. *)
(*   all: simpl in H. *)
(*   all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto]. *)
(*   all: try auto 2. *)
(*   - simpl in *. *)
(*     have: x `notin` fv_tm_tm_tm (open_tm_wrt_tm a' b') => h0. *)
(*     apply fv_tm_tm_tm_open_tm_wrt_tm_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     fsetdec_fast. *)
(*     fsetdec_fast. *)
(*     auto. *)
(*   - rewrite fv_tm_tm_tm_open_tm_wrt_co_upper. *)
(*     fsetdec. *)
(*   (* - rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. *) *)
(*   (*   fsetdec. *) *)
(*   (* - have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' g_Triv) => h0. *) *)
(*   (*   apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0. *) *)
(*   (*   apply AtomSetFacts.union_iff in h0. *) *)
(*   (*   case:h0; eauto => h0. *) *)
(*   (*   fsetdec. *) *)
(*   (*   auto. *) *)
(*   - pick fresh x0. *)
(*     assert (Fl : x0 `notin` L). auto. *)
(*     assert (Fa : x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x0))). *)
(*     rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. auto. *)
(*     move: (H x0 Fl Fa) => h0. *)
(*     rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.  *)
(*   - pick fresh x0. *)
(*     have na': x `notin` fv_tm_tm_tm A'. eauto. *)
(*     have nb: x `notin` fv_tm_tm_tm (open_tm_wrt_tm B (a_Var_f x0)). *)
(*     rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. eauto. *)
(*     have nob': x `notin` fv_tm_tm_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto. *)
(*     have nb': x `notin` fv_tm_tm_tm B'. *)
(*     rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. *)
(*     eauto. *)
(*   - pick_fresh c0. *)
(*     have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0. *)
(*     apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     simpl in h0. *)
(*     fsetdec. *)
(*     have K:= H c0 ltac:(auto) h0. *)
(*     move => h1. *)
(*     apply K. auto. *)
(*     apply fv_tm_tm_tm_open_tm_wrt_co_lower; auto. *)
(*   - pick fresh c0 for L. *)
(*     have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0. *)
(*     apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     simpl in h0. *)
(*     fsetdec. *)
(*     have h2: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' (g_Var_f c0)). eauto. *)
(*     move: (fv_tm_tm_tm_open_tm_wrt_co_lower a' (g_Var_f c0)) => h3. fsetdec. *)
(*   - move : b H => H. *)
(*     apply toplevel_closed in H. *)
(*     move: (Typing_context_fv H) => ?. split_hyp. *)
(*     simpl in *. *)
(*     fsetdec. *)
(*   - move : H e => IHPar H1. *)
(*     apply IHPar. *)
(*     pick fresh y. *)
(*     move: (H1 y ltac:(auto)) => h0. *)
(*     apply (fun_cong fv_tm_tm_tm) in h0. *)
(*     simpl in h0. *)
(*     move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1. *)
(*     move: (@fv_tm_tm_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2. *)
(*     unfold not. intro IN. *)
(*     assert (h3: x `in` (union (fv_tm_tm_tm b) (singleton y))). auto. *)
(*     rewrite -h0 in h3. *)
(*     apply h2 in h3. *)
(*     simpl in h3. *)
(*     destruct (AtomSetImpl.union_1 h3). *)
(*     assert (x `notin` singleton y). auto. done. *)
(*     done. *)
(*   - move : H e => IHPar H1. *)
(*     apply IHPar. *)
(*     pick fresh y. *)
(*     move: (H1 y ltac:(auto)) => h0. *)
(*     apply (fun_cong fv_tm_tm_tm) in h0. *)
(*     simpl in h0. *)
(*     move: (@fv_tm_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1. *)
(*     move: (@fv_tm_tm_tm_open_tm_wrt_co_upper a (g_Var_f y) x) => h2. *)
(*     unfold not. intro IN. *)
(*     assert (h3: x `in` (union (fv_tm_tm_tm b) empty)). auto. *)
(*     rewrite -h0 in h3. *)
(*     apply h2 in h3. *)
(*     simpl in h3. *)
(*     destruct (AtomSetImpl.union_1 h3). fsetdec. *)
(*     assert (x `notin` singleton y). auto. done. *)
(*   - admit. *)
(*   -  *)
(*   - move : H e => IHPar H1. *)
(*     apply IHPar. *)
(*     pick fresh y. *)
(*     move: (H1 y ltac:(auto)) => h0. *)
(*     apply (fun_cong fv_tm_tm_tm) in h0. *)
(*     simpl in h0. *)
(*     move: (@fv_tm_tm_tm_open_tm_wrt_co_lower a (g_Var_f y) x) => h1. *)
(*     move: (@fv_tm_tm_tm_open_tm_wrt_co_upper a (g_Var_f y) x) => h2. *)
(*     unfold not. intro IN. *)
(*     assert (h3: x `in` (union (fv_tm_tm_tm b) empty)). auto. *)
(*     rewrite -h0 in h3. *)
(*     apply h2 in h3. *)
(*     simpl in h3. *)
(*     destruct H0.  *)
(*     apply AtomSetProperties.empty_union_1 in h3. *)
(*     auto. done. *)
(* Qed. *)

(* Lemma Par_fv_co_preservation: forall x, (forall G D a b, Par G D a b -> *)
(*                                         x `notin` fv_co_co_tm a -> *)
(*                                         x `notin` fv_co_co_tm b) /\ *)
(*                                    (forall G D phi1 phi2, ParProp G D phi1 phi2 -> *)
(*                                         x `notin` fv_co_co_constraint phi1 -> *)
(*                                         x `notin` fv_co_co_constraint phi2). *)
(* Proof. *)
(*   move => x. *)
(*   apply Par_tm_constraint_mutual; intros; eauto 2; simpl. *)
(*   all: simpl in *. *)
(*   all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto]. *)
(*   all: try auto. *)
(*   - simpl in *. *)
(*     have: x `notin` fv_co_co_tm (open_tm_wrt_tm a' b') => h0. *)
(*     apply fv_co_co_tm_open_tm_wrt_tm_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     fsetdec_fast. *)
(*     fsetdec_fast. *)
(*     auto. *)
(*   - rewrite fv_co_co_tm_open_tm_wrt_tm_upper. *)
(*     fsetdec. *)
(*   - have: x `notin` fv_co_co_tm (open_tm_wrt_co a' g_Triv) => h0. *)
(*     apply fv_co_co_tm_open_tm_wrt_co_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     fsetdec. *)
(*     auto. *)
(*   - move : H => H1. *)
(*     pick fresh x0. *)
(*     assert (Fl : x0 `notin` L). auto. *)
(*     assert (Fa : x `notin` fv_co_co_tm (open_tm_wrt_tm a (a_Var_f x0))). *)
(*     rewrite fv_co_co_tm_open_tm_wrt_tm_upper. auto. *)
(*     move: (H1 x0 Fl Fa) => h0. *)
(*     rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto.  *)
(*   - pick fresh x0. *)
(*     have na': x `notin` fv_co_co_tm A'. eauto. *)
(*     have nb: x `notin` fv_co_co_tm (open_tm_wrt_tm B (a_Var_f x0)). *)
(*     rewrite fv_co_co_tm_open_tm_wrt_tm_upper. eauto. *)
(*     have nob': x `notin` fv_co_co_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto. *)
(*     have nb': x `notin` fv_co_co_tm B'. *)
(*     rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto. *)
(*     eauto. *)
(*   - move : H => H1. *)
(*     pick_fresh c0. *)
(*     have: x `notin` fv_co_co_tm (open_tm_wrt_co a (g_Var_f c0)) => h0. *)
(*     apply fv_co_co_tm_open_tm_wrt_co_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     simpl in h0. *)
(*     fsetdec. *)
(*     have K:= H1 c0 ltac:(auto) h0. *)
(*     move => h1. *)
(*     apply K. auto. *)
(*     apply fv_co_co_tm_open_tm_wrt_co_lower; auto. *)
(*   - pick fresh c0. *)
(*     have: x `notin` fv_co_co_tm (open_tm_wrt_co a (g_Var_f c0)) => h0. *)
(*     apply fv_co_co_tm_open_tm_wrt_co_upper in h0. *)
(*     apply AtomSetFacts.union_iff in h0. *)
(*     case:h0; eauto => h0. *)
(*     destruct_notin. *)
(*     simpl in h0. fsetdec. *)
(*     simpl in h0. assert (Q: c0 `notin` singleton x). fsetdec. *)
(*     destruct_notin. *)
(*     have h2: x `notin` fv_co_co_tm (open_tm_wrt_co a' (g_Var_f c0)). eauto. *)
(*     move: (fv_co_co_tm_open_tm_wrt_co_lower a' (g_Var_f c0)) => h3. *)
(*     have h4: x `notin` fv_co_co_tm a'. fsetdec. *)
(*     fsetdec. *)
(*   - move : b H => H.             (* rename b to H and remove the original H *) *)
(*     apply toplevel_closed in H. *)
(*     move: (Typing_context_fv H) => ?. split_hyp. *)
(*     simpl in *. *)
(*     fsetdec. *)
(*   - move : H e => IHPar H1. *)
(*     apply IHPar. *)
(*     pick fresh y. *)
(*     move: (H1 y ltac:(auto)) => h0. *)
(*     apply (fun_cong fv_co_co_tm) in h0. *)
(*     simpl in h0. *)
(*     move: (@fv_co_co_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1. *)
(*     move: (@fv_co_co_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2. *)
(*     unfold not. intro IN. *)
(*     assert (h3: x `in` (union (fv_co_co_tm b) empty)). auto. *)
(*     rewrite -h0 in h3. *)
(*     apply h2 in h3. *)
(*     simpl in h3. *)
(*     destruct (AtomSetImpl.union_1 h3). *)
(*     assert (x `notin` singleton y). auto. fsetdec. fsetdec. *)
(*   - move : H e => IHPar H1. *)
(*     apply IHPar. *)
(*     pick fresh y. *)
(*     move: (H1 y ltac:(auto)) => h0. *)
(*     apply (fun_cong fv_co_co_tm) in h0. *)
(*     simpl in h0. *)
(*     move: (@fv_co_co_tm_open_tm_wrt_tm_lower a (a_Var_f y) x) => h1. *)
(*     move: (@fv_co_co_tm_open_tm_wrt_tm_upper a (a_Var_f y) x) => h2. *)
(*     unfold not. intro IN. *)
(*     assert (h3: x `in` (union (fv_co_co_tm b) empty)). auto. *)
(*     rewrite -h0 in h3. *)
(*     apply h2 in h3. *)
(*     simpl in h3. *)
(*     destruct (AtomSetImpl.union_1 h3). *)
(*     assert (x `notin` singleton y). auto. fsetdec. fsetdec. *)
(*   - move : H e => IHPar H1. *)
(*     apply IHPar. *)
(*     pick fresh y. *)
(*     move: (H1 y ltac:(auto)) => h0. *)
(*     apply (fun_cong fv_co_co_tm) in h0. *)
(*     simpl in h0. *)
(*     move: (@fv_co_co_tm_open_tm_wrt_co_lower a (g_Var_f y) x) => h1. *)
(*     move: (@fv_co_co_tm_open_tm_wrt_co_upper a (g_Var_f y) x) => h2. *)
(*     unfold not. intro IN. *)
(*     assert (h3: x `in` (union (fv_co_co_tm b) empty)). auto. *)
(*     rewrite -h0 in h3. *)
(*     apply h2 in h3. *)
(*     simpl in h3. destruct (AtomSetImpl.union_1 h3). *)
(*     assert (x `notin` singleton y). auto. fsetdec. fsetdec. *)
(* Qed. *)

Lemma Par_erased_tm_constraint_mutual :
  (forall P1 psi a a', Par P1 psi a a' -> forall (Ea : erased_tm a), erased_tm a') /\
  (forall P1 psi phi phi', ParProp P1 psi phi phi' -> forall (Ephi : erased_constraint phi),  erased_constraint phi') /\
    (forall P1 psi psi0 a a', CPar P1 psi psi0 a a' -> erased_tm a -> erased_tm a') /\
    (forall P1 psi psi0 phi1 phi2, CParProp P1 psi psi0 phi1 phi2 -> erased_constraint phi1 ->  erased_constraint phi2).
Proof.
  apply Par_tm_constraint_mutual; intros; try inversion Ea; try inversion Ephi; subst; eauto.
  all: try solve [ erased_pick_fresh x; auto ].
  all: eauto with erased.
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (tm_subst_tm_tm_intro x); auto;
    apply subst_tm_erased; auto.
  (* - move: (H ltac:(auto)); inversion 1; *)
  (*   pick fresh x; *)
  (*   rewrite (tm_subst_tm_tm_intro x); auto; *)
  (*   apply subst_tm_erased; auto. *)
  - move: (H ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (co_subst_co_tm_intro x); auto;
      apply subst_co_erased_tm; auto.
  (* - apply erased_a_Abs with (L := union L L0). intros. eauto. *)
  (*   intros. assert (W: x `notin` L0). fsetdec. apply H3 in W. *)
  (*   inversion W; subst. econstructor; eauto. *)
  (*   econstructor. eapply Par_fv_preservation in H1; eauto. *)
  - pick fresh c0.
    destruct_notin.
    move: (e c0 ltac:(auto)) => h0.
    move: (H1 c0 ltac:(auto))  => h1.
    rewrite h0 in h1.
    inversion h1; auto.
  - pick fresh c0.
    destruct_notin.
    move: (e c0 ltac:(auto)) => h0.
    move: (H1 c0 ltac:(auto))  => h1.
    rewrite h0 in h1.
    inversion h1; auto.
  (* not provable until spec is fixed *)
  - admit.
  (* not provable until spec is fixed *)
  - admit.
Admitted.

Lemma Par_erased_tm : forall P psi a a', Par P psi a a' -> forall (Ea : erased_tm a), erased_tm a'.
Proof.
  apply Par_erased_tm_constraint_mutual.
Qed.

Lemma Par_erased_constraint : forall P psi phi phi', ParProp P psi phi phi' -> forall (Ephi : erased_constraint phi),  erased_constraint phi'.
Proof.
  apply Par_erased_tm_constraint_mutual.
Qed.

#[export] Hint Resolve Par_erased_tm Par_erased_constraint : erased. 

(* ------------------------------------------------------------- *)


(* The subst theorem now requires well-gradedness *)
(* check the proofs from DDC *)
Lemma subst1 : forall P psi a a' x, Par P psi a a' -> 
                             (forall b, erased_tm b ->
                               Par P psi (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b)) /\
                             (forall phi, erased_constraint phi ->
                               ParProp P psi (tm_subst_tm_constraint a x phi) (tm_subst_tm_constraint a' x phi)).
Proof.
  move => P psi a a' x PAR; apply erased_tm_constraint_mutual; intros; simpl; eauto.
  sauto lq:on use:Par_ECtx.
  destruct (x0 == x); subst. auto.
  best use:Par_ECtx.

  
  all: try solve [Par_pick_fresh y;
                  autorewrite with subst_open_var; eauto with lc].
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

Lemma context_Par_irrelevance_tm: forall G1 D1 a a',
                                             Par G1 D1 a a' -> forall G2 D2, Par G2 D2 a a'.
Proof.
  apply context_Par_irrelevance.
Qed.


Lemma context_multipar_irrelevance: forall G1 D1 a a', multipar G1 D1 a a' -> forall G2 D2, multipar G2 D2 a a'.
Proof.
  induction 1; eauto.
  intros.
  apply mp_step with (b := b); auto.
  eapply context_Par_irrelevance; eauto.
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

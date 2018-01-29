Require Export FcEtt.ett_inf_cs.
Require Export FcEtt.ett_ind.

Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


(* Syntactic properties about the erasure operation.
   TODO: add these to a hint database?
   -------------------------------------------------

   erase (open t u) = open (erase t) (erase u)

   erase (open_co t g) = erase t
   erase (open_co t g) = open_co (erase t) g

   x notin fv t -> x notin fv (erase t)

   erase (close x t) = close x (erase t)

   erase (subst x u t) = subst x (erase u) (erase t)

   lc u -> lc (erase u)

   dom G = dom (erase_context G)

 *)




(* ----- open ---------- *)

(* In general: erase (open t u) = open (erase t) (erase u) *)

Lemma open_tm_erase_rec : forall a,
  (forall b k R, open_tm_wrt_tm_rec k (erase a R) (erase b R) =
                 erase (open_tm_wrt_tm_rec k a b) R) /\
  (forall b k R, open_brs_wrt_tm_rec k (erase a R) (erase b R) =
                 erase (open_brs_wrt_tm_rec k a b) R) /\
  (forall g:co, True) /\
  (forall b k R, open_constraint_wrt_tm_rec k (erase a R) (erase b R) =
                 erase (open_constraint_wrt_tm_rec k a b) R).
Proof.
  move=> a.
  eapply tm_brs_co_constraint_mutind;
  intros; simpl; auto;
  try (rewrite H; try rewrite H0; auto).
  case (lt_eq_lt_dec n k);
    try (move=> []); simpl; auto.
  all: f_equal; simpl; eauto 3.
  - destruct rho.
  + simpl; auto. autorewcs. f_equal; eauto.  (* rewrite H0.  rewrite H. auto. *)
  + simpl; auto. f_equal; eauto. (* rewrite H.  auto. *)
  - destruct R, R0; simpl; eauto. rewrite H; auto.
Qed.


Lemma open_tm_erase_tm : forall a b R,
  open_tm_wrt_tm (erase a R) (erase b R) =
                 erase (open_tm_wrt_tm a b) R.
Proof.
  move=> a b. intro.
  case (open_tm_erase_rec b R).
  unfold open_tm_wrt_tm.
  eauto.
Qed.



Lemma open_co_erase_rec : forall a R,
  (forall b k, (erase b R) =
                 erase (open_tm_wrt_co_rec k a b) R) /\
  (forall b k, (erase b R) =
                 erase (open_brs_wrt_co_rec k a b) R) /\
  (forall g:co, True) /\
  (forall b k, (erase b R) =
                 erase (open_constraint_wrt_co_rec k a b) R).
Proof.
  move=> a. intro.
  eapply tm_brs_co_constraint_mutind;
  intros; unfold Operators.erase'; simpl; auto; (* FIXME: not sure having to do <unfold erase'> is right *)
    try (rewrite <- H; try rewrite <- H0; auto).
  all: f_equal; eauto 2.
Qed.

Lemma open_co_erase_tm : forall a b R,
  (erase b R) = erase (open_tm_wrt_co b a) R.
Proof.
  move=> a b. intro.
  destruct (open_co_erase_rec a R).
  unfold open_tm_wrt_co.
  eauto.
Qed.


Lemma open_co_erase2_rec : forall a R,
  (forall b k g, (open_tm_wrt_co_rec k g (erase b R)) =
                 erase (open_tm_wrt_co_rec k a b) R) /\
  (forall b k g, (open_brs_wrt_co_rec k g (erase b R)) =
                 erase (open_brs_wrt_co_rec k a b) R) /\
  (forall g:co, True) /\
  (forall b k g, (open_constraint_wrt_co_rec k g (erase b R)) =
                 erase (open_constraint_wrt_co_rec k a b) R).
Proof.
  move=> a. intro.
  eapply tm_brs_co_constraint_mutind;
  intros; try (destruct rho); unfold Operators.erase'; simpl; auto;
  f_equal; auto;
    try (autorewcs; rewrite <- H; try rewrite <- H0; auto).
  destruct R, R0; simpl; eauto. rewrite H; auto.
Qed.


Lemma open_co_erase_tm2 : forall a b R g,
  (open_tm_wrt_co (erase b R) g) = erase (open_tm_wrt_co b a) R.
Proof.
  move=> a b. intro.
  case (open_co_erase2_rec a R).
  unfold open_tm_wrt_co.
  eauto.
Qed.

Corollary no_co_in_erased_tm : forall B R g,
 open_tm_wrt_co (erase B R) g = erase B R.
 Proof.
  intros.
  rewrite (open_co_erase_tm2 g_Triv).
  rewrite <- open_co_erase_tm.
  done.
Qed.




(* ----- close ----------------- *)

Lemma close_tm_erase_all : ∀ (x : tmvar) R,
  (∀ (a : tm)         k, close_tm_rec k x (erase a R) = erase (close_tm_rec k x a) R) /\
  (∀ (b : brs)        k, close_tm_rec k x (erase b R) = erase (close_tm_rec k x b) R) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_tm_rec k x (erase c R) = erase (close_tm_rec k x c) R).
Proof.
  move => x R; simpl;
  apply tm_brs_co_constraint_mutind;
  basic_nosolve_fo'.
  - case (lt_ge_dec n k); done.
  - move eqe : (x == x0) => [] // .
  - destruct rho; basic_solve_fo'.
  - destruct R, R0; eauto.
Qed.

Lemma close_co_erase_all : ∀ (x : covar) R,
  (∀ (a : tm)         k, close_co_rec k x (erase a R) = erase (close_co_rec k x a) R) /\
  (∀ (b : brs)        k, close_co_rec k x (erase b R) = erase (close_co_rec k x b) R) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_co_rec k x (erase c R) = erase (close_co_rec k x c) R).
Proof.
  move => x R; simpl;
  apply tm_brs_co_constraint_mutind.
  all : basic_nosolve_fo'.
  solve [case (lt_ge_dec n k); done | move eqe : (x == x0) => [] // | destruct rho; basic_solve_fo'].
  destruct R, R0; eauto.
Qed.

Definition close_tm_rec_erase_tm := fun x R => proj1 (close_tm_erase_all x R).
Definition close_co_rec_erase_tm := fun x R => proj1 (close_co_erase_all x R).

Lemma close_tm_erase_tm
     : ∀ (x : tmvar) (a : tm) R, close_tm x (erase a R) = erase (close_tm x a) R.
Proof.
  intros. eapply close_tm_rec_erase_tm.
Qed.

Lemma close_co_erase_tm
  : ∀ (x : covar) (a : tm) R, close_co x (erase a R) = erase (close_co x a) R.
Proof.
  intros. eapply close_co_rec_erase_tm.
Qed.

(* This proof method is cool, but it is hard to extract the result in a way we can use

(* TODO: with an approriate mutual induction tactic, could be proved only with a : tm + brs + co + constraint *)
Lemma close_tmco_erase_all : ∀ (x : tmvar + covar),
  (∀ (a : tm)         k, close_wrt k x (erase a) = erase (close_wrt k x a)) /\
  (∀ (b : brs)        k, close_wrt k x (erase b) = erase (close_wrt k x b)) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_wrt k x (erase c) = erase (close_wrt k x c)).
Proof.
  move => [] x; simpl;
  apply tm_brs_co_constraint_mutind;
  basic_nosolve_fo';
  solve [case (lt_ge_dec n k); done | move eqe : (x == x0) => [] // | basic_solve_fo'].
Qed.

Definition close_tm_erase_all := fun x => close_tmco_erase_all (inl x).
Definition close_co_erase_all := fun x => close_tmco_erase_all (inr x).

Definition close_tm_erase_tm := fun x => proj1 (close_tm_erase_all x).
Definition close_co_erase_tm := fun x => proj1 (close_co_erase_all x).
*)

(* Pointless to close erased terms wrt co variables *)

Lemma close_co_erase_rec : ∀ (x : covar) R,
  (∀ (a : tm)         k, close_co_rec k x (erase a R) = erase a R) /\
  (∀ (b : brs)        k, close_co_rec k x (erase b R) = erase b R) /\
  (∀ _ : co, True) /\
  (∀ (c : constraint) k, close_co_rec k x (erase c R) = erase c R).
Proof.
  move => x R; simpl;
  apply tm_brs_co_constraint_mutind.
  all: basic_nosolve_fo'.
  solve [case (lt_ge_dec n k); done | move eqe : (x == x0) => [] // | destruct rho; basic_solve_fo'].
  destruct R, R0; simpl; eauto. rewrite H. auto.
Qed.

Lemma close_co_erase_tm2 : forall x a R, close_tm_wrt_co x (erase a R) = erase a R.
Proof.
  intros x a R.
  eapply (close_co_erase_rec x R).
Qed.





(* ----- fv  ---------- *)

Lemma fv_tm_erase_tm : ∀ x R (a : tm),
    x `notin` fv_tm a -> x `notin` fv_tm (erase a R).
Proof.
  move=> x R.
  (* TODO: should be done automatically (mutual induction tactic) *)
  cut ((∀ a : tm, x `notin` fv_tm a -> x `notin` fv_tm (erase a R)) /\
       (∀ a : brs, x `notin` fv_tm a -> x `notin` fv_tm (erase a R)) /\
       (∀ a : co, x `notin` fv_tm a -> x `notin` fv_tm (erase a R)) /\
       (∀ a : constraint, x `notin` fv_tm a -> x `notin` fv_tm (erase a R))).
    by move=> [a _].
    eapply tm_brs_co_constraint_mutind; try (destruct rho); basic_solve_fo'.
    intros.  destruct R, R0; simpl; basic_solve_fo'.
Qed.


Lemma fv_co_erase_tm : ∀ x R (a : tm),
    x `notin` fv_co a -> x `notin` fv_co (erase a R).
Proof.
  move=> x R.
  (* TODO: should be done automatically (mutual induction tactic) *)
  cut ((∀ a : tm, x `notin` fv_co a -> x `notin` fv_co (erase a R)) /\
       (∀ a : brs, x `notin` fv_co a -> x `notin` fv_co (erase a R)) /\
       (∀ a : co, x `notin` fv_co a -> x `notin` fv_co (erase a R)) /\
       (∀ a : constraint, x `notin` fv_co a -> x `notin` fv_co (erase a R))).
    by move=> [a _].
    eapply tm_brs_co_constraint_mutind; try (destruct rho); basic_solve_fo'.
    intros. destruct R, R0; simpl; basic_solve_fo'.
Qed.


(* ----- substitution ---------- *)

Lemma subst_tm_erase : forall a x R,
  (forall b, tm_subst_tm_tm (erase a R) x (erase b R) =
              erase (tm_subst_tm_tm a x b) R) /\
  (forall b, tm_subst_tm_brs (erase a R) x (erase b R) =
              erase (tm_subst_tm_brs a x b) R) /\
  (forall g:co, True) /\
  (forall p, tm_subst_tm_constraint (erase a R) x (erase p R) =
              erase (tm_subst_tm_constraint a x p) R).
Proof.
  move=> a x R.
  eapply tm_brs_co_constraint_mutind;
  intros; simpl; auto;
  try (rewrite H; try rewrite H0; auto).
  destruct (x0 == x); simpl; auto.
  all: f_equal; eauto 2.
  destruct rho; simpl; f_equal; eauto 2.
  destruct R, R0; eauto. simpl; rewrite H; auto.
Qed.

Lemma subst_co_erase : forall a x R,
  (forall b, (erase b R) =
              erase (co_subst_co_tm a x b) R) /\
  (forall b, (erase b R) =
              erase (co_subst_co_brs a x b) R) /\
  (forall g:co, True) /\
  (forall p, (erase p R) =
              erase (co_subst_co_constraint a x p) R).
Proof.
  intros a x R.
  eapply tm_brs_co_constraint_mutind;
  intros;  unfold Operators.erase'; simpl; autorewcs; auto;
    try (rewrite <- H; try rewrite <- H0; auto).
  all: f_equal; eauto 2.
Qed.

Lemma subst_tm_erase_tm:  forall a x R b,
    tm_subst_tm_tm (erase a R) x (erase b R) =
              erase (tm_subst_tm_tm a x b) R.
Proof.
  intros a R x.
  destruct (subst_tm_erase a R x).
  eauto.
Qed.

Lemma subst_co_erase_tm : forall a x R b,
    (erase b R) =
    erase (co_subst_co_tm a x b) R.
Proof.
  intros a x R.
  destruct (subst_co_erase a x R).
  eauto.
Qed.




(* ----- Preservation of erasure under substitution ---------- *)

Theorem erase_subst_mutual a x R0:
  (∀ A B,       erase_tm A R0 = erase_tm B R0 ->
                  erase_tm (tm_subst_tm_tm a x A) R0 = erase_tm (tm_subst_tm_tm a x B) R0)
  ∧
  (∀ Bs1 Bs2,   erase_brs Bs1 R0 = erase_brs Bs2 R0 ->
                  erase_brs (tm_subst_tm_brs a x Bs1) R0 =
                  erase_brs (tm_subst_tm_brs a x Bs2) R0)
  ∧
  (∀ g1 g2 : co, True)
  ∧
  (∀ phi1 phi2, erase_constraint phi1 R0 = erase_constraint phi2 R0 ->
                  erase_constraint (tm_subst_tm_constraint a x phi1) R0 =
                  erase_constraint (tm_subst_tm_constraint a x phi2) R0).
Proof.
  apply tm_brs_co_constraint_mutind  =>
    //
    (* tm *)
    [ (* star *)
    | i | y
    | rho ty IHty R body IHbody | rho e R IH | e1 IH1 rho R e2 IH2
    | f | k
    | rho A1 IH1 R A2 IH2
    (* cast *)
    | g IHg R1 A IHA | g IHg e IHe | g IHg e IHe | e IH | e IHe g IHg
    | (* bullet *)
    | con | e IH Bs IHBs
    (* brs *)
    | (* br_None *)
    | con e IHe Bs IHBs
    (* constraint *)
    | A IHA B IHB ].
  all: match goal with
       | |- constraint → _ =>
         case => [A' B']
       | |- tm         → _ =>
         elim =>  [ (* star *)
                 | i' | y'
                 | rho' ty' IHty' R' body' IHbody' | rho' e' R' IH' | e1' IH1' rho' R' e2' IH2'
                 | f' | k'
                 | rho' A1' IH1' R1' A2' IH2'
                 | e' IHe' R1' g'
                 | g' A' IHA' | g' e' IHe' | e' IH' | e' IHe' g'
                 | (* bullet *)
                 | con' | e' IH' Bs' | R1' e' IHe'
                 ]
       | |- brs        → _ =>
         case => [ | con' e' Bs' ]
       | |- _ => idtac
       end.

  all: try (destruct R1, R0; try apply IHg; destruct g; 
            intro H; inversion H; apply IHg).
  all: try (destruct R1', R0; try apply IHe'; destruct e';
            intro H; inversion H; apply IHe').
  all: try (destruct R1, R0; eauto; destruct rho', R'; intro; 
           simpl in *; destruct g; simpl in H; inversion H; eauto).
  all: try (destruct R1', R0; eauto; destruct rho, R; intro; 
           simpl in *; destruct e'; simpl in H; inversion H; eauto).
  all: try (destruct R1, R0, R1'; auto; simpl in *; 
            intro H; inversion H; pose (P := IHg e' H1); rewrite P; auto).
  all: try (try (destruct rho); try (destruct rho'); move=> //= [] *; try subst; f_equal; eauto).
  all: intros.
  all: destruct phi2.
  all: simpl.
  all: simpl in H0.
  all: inversion H0; subst.
  all: try erewrite IHB; eauto.
  all: try erewrite IHA; eauto.
  all: simpl in H.
  all: try erewrite H; eauto.
Qed.

Corollary erase_subst_constraint phi1 phi2 a x R :
  erase_constraint phi1 R = erase_constraint phi2 R ->
    erase_constraint (tm_subst_tm_constraint a x phi1) R =
    erase_constraint (tm_subst_tm_constraint a x phi2) R.
Proof. move: (erase_subst_mutual a x R) => ?; split_hyp; auto. Qed.

Corollary erase_subst_tm A B a x R :
  erase_tm A R = erase_tm B R ->
  erase_tm (tm_subst_tm_tm a x A) R = erase_tm (tm_subst_tm_tm a x B) R.
Proof. move: (erase_subst_mutual a x R) => ?; split_hyp; auto. Qed.

Corollary erase_subst_brs Bs1 Bs2 a x R :
  erase_brs Bs1 R = erase_brs Bs2 R ->
  erase_brs (tm_subst_tm_brs a x Bs1) R = erase_brs (tm_subst_tm_brs a x Bs2) R.
Proof. move: (erase_subst_mutual a x R) => ?; split_hyp; auto. Qed.

Theorem erase_co_subst_co_mutual a x R0 :
  (∀ A B,       erase_tm A R0 = erase_tm B R0 ->
                  erase_tm (co_subst_co_tm a x A) R0 = erase_tm (co_subst_co_tm a x B) R0)
  ∧
  (∀ Bs1 Bs2,   erase_brs Bs1 R0 = erase_brs Bs2 R0 ->
                  erase_brs (co_subst_co_brs a x Bs1) R0 =
                  erase_brs (co_subst_co_brs a x Bs2) R0)
  ∧
  (∀ g1 g2 : co, True)
  ∧
  (∀ phi1 phi2, erase_constraint phi1 R0 = erase_constraint phi2 R0 ->
                  erase_constraint (co_subst_co_constraint a x phi1) R0 =
                  erase_constraint (co_subst_co_constraint a x phi2) R0).
Proof.
  apply tm_brs_co_constraint_mutind =>
    //
    (* tm *)
    [ (* star *)
    | i | y
    | rho ty IHty R body IHbody | rho e R IH | e1 IH1 rho R e2 IH2
    | f | k
    | rho A1 IH1 R1 A2 IH2
    (* cast was solved auto *)
    | g IHg R1 A IHA | g IHg e IHe | g IHg e IHe | e IH | e IHe g IHg
    | (* bullet *)
    | con | e IH Bs IHBs
    (* brs *)
    | (* br_None *)
    | con e IHe Bs IHBs
    (* constraint *)
    | A IHA B IHB ].
  all: match goal with
       | |- constraint → _ =>
         case => [A' B']
       | |- tm         → _ =>
         elim => [ (* star *)
                 | i' | y'
                 | rho' ty' IHty' R' body' IHbody' | rho' e' R' IH' | e1' IH1' rho' R' e2' IH2'
                 | f' | k'
                 | rho' A1' IH1' R' A2' IH2'
                 | e' IHe' R1' g'
                 | g' A' IHA' | g' e' IHe' | e' IH' | e' IHe' g'
                 | (* bullet *)
                 | con' | e' IH' Bs' | R1' e' IHe'
                 ]
       | |- brs        → _ =>
         case => [ | con' e' Bs' ]
       end.
  all: try (destruct R1, R0; try apply IHg; destruct g; 
            intro H; inversion H; apply IHg).
  all: try (destruct R1', R0; try apply IHe'; destruct e';
            intro H; inversion H; apply IHe').
  all: try (destruct R1, R0; eauto; destruct rho', R'; intro; 
           simpl in *; destruct g; simpl in H; inversion H; eauto).
  all: try (destruct R1', R0; eauto; destruct rho, R; intro; 
           simpl in *; destruct e'; simpl in H; inversion H; eauto).
  all: try (destruct R1, R0, R1'; auto; simpl in *; 
            intro H; inversion H; pose (P := IHg e' H1); rewrite P; auto).
  all: try solve [try destruct rho; try destruct rho'; move=> //= [] *; try subst; f_equal; eauto].
  all: intros.
  all: try destruct phi2.
  all: simpl.
  all: try simpl in H0.
  all: try inversion H0; subst.
  all: try erewrite IHB; eauto.
  all: try erewrite IHA; eauto.
  all: simpl in H.
  all: try erewrite H; eauto.
Qed.

Corollary erase_co_subst_constraint phi1 phi2 a x R :
  erase_constraint phi1 R = erase_constraint phi2 R ->
    erase_constraint (co_subst_co_constraint a x phi1) R =
    erase_constraint (co_subst_co_constraint a x phi2) R.
Proof. move: (erase_co_subst_co_mutual a x R) => ?; split_hyp; auto. Qed.

Corollary erase_co_subst_tm A B a x R :
  erase_tm A R = erase_tm B R ->
  erase_tm (co_subst_co_tm a x A) R = erase_tm (co_subst_co_tm a x B) R.
Proof. move: (erase_co_subst_co_mutual a x R) => ?; split_hyp; auto. Qed.

Corollary erase_co_subst_brs Bs1 Bs2 a x R :
  erase_brs Bs1 R = erase_brs Bs2 R ->
  erase_brs (co_subst_co_brs a x Bs1) R = erase_brs (co_subst_co_brs a x Bs2) R.
Proof. move: (erase_co_subst_co_mutual a x R) => ?; split_hyp; auto. Qed.





(* ----- local closure ---------- *)

Lemma lc_erase : forall R,
  (forall a, lc_tm a -> lc_tm (erase a R)) /\
  (forall b, lc_brs b -> lc_brs (erase b R)) /\
  (forall (g:co) (l:lc_co g), True) /\
  (forall b, lc_constraint b -> lc_constraint (erase b R)).
Proof. intro R.
  eapply lc_tm_lc_brs_lc_co_lc_constraint_mutind.
  all: intros.
  all: try solve [try destruct rho; simpl; eauto].
  - apply lc_a_UAbs. auto.
    intro x.
    assert (HV : erase (a_Var_f x) R = a_Var_f x). auto.
    rewrite <- HV.
    rewrite open_tm_erase_tm. auto.
  - apply lc_a_UAbs. auto.
    intro x.
    assert (HV : erase (a_Var_f x) R = a_Var_f x). auto.
    rewrite <- HV.
    rewrite open_tm_erase_tm. auto.
  - apply lc_a_Pi. auto.
    intro x.
    assert (HV : erase (a_Var_f x) R = a_Var_f x). auto.
    rewrite <- HV.
    rewrite open_tm_erase_tm. auto.
  - destruct R, R0; eauto. 
    simpl. apply lc_a_Conv; eauto.
  - apply lc_a_CPi. auto.
    intro c.
    rewrite (open_co_erase_tm2 (g_Var_f c)).
    auto.
  - apply lc_a_UCAbs. auto.
    intro c.
    rewrite (open_co_erase_tm2 (g_Var_f c)).
    auto.
  - apply lc_a_UCAbs. auto.
    intro c.
    rewrite (open_co_erase_tm2 (g_Var_f c)).
    auto.
Qed.

Lemma lc_tm_erase : (forall a R, lc_tm a -> lc_tm (erase a R)).
intros. eapply lc_erase. auto. Qed.

Lemma lc_brs_erase : (forall b R, lc_brs b -> lc_brs (erase b R)).
intros. eapply lc_erase. auto. Qed.

Lemma lc_constraint_erase : (forall b R, lc_constraint b -> lc_constraint (erase b R)).
intros. eapply lc_erase. auto. Qed.

Hint Resolve lc_tm_erase lc_brs_erase lc_constraint_erase : lc.

Lemma lc_tm_open_tm_wrt_tm_erase_tm : forall a R,
    (∀ x, lc_tm (open_tm_wrt_tm a (a_Var_f x))) ->
    forall x, lc_tm (open_tm_wrt_tm (erase_tm a R) (a_Var_f x)).
Proof.
  intros.
  replace (a_Var_f x) with (erase (a_Var_f x) R); auto.
  rewrite open_tm_erase_tm.
  apply lc_erase. auto.
Qed.

Lemma lc_tm_open_tm_wrt_co_erase_tm : forall a R,
    (∀ x, lc_tm (open_tm_wrt_co a (g_Var_f x))) ->
    forall x, lc_tm (open_tm_wrt_co (erase_tm a R) (g_Var_f x)).
Proof.
  intros.
  rewrite (open_co_erase_tm2 (g_Var_f x)).
  eauto with lc.
Qed.



Hint Resolve lc_tm_open_tm_wrt_tm_erase_tm lc_tm_open_tm_wrt_co_erase_tm : lc.

(* ----- automation ---------- *)

(* TODO *)
Hint Rewrite open_co_erase_tm open_co_erase_tm2 open_tm_erase_tm : TODO.
Hint Resolve lc_erase binds_map_2.



Ltac auto_rew_erase :=
  multimatch goal with
    | [ e: erase _ _ = erase _ _ |- _ ] => rewrite e in *; clear e
  end.




(* ----- useful property for pi types -------------- *)

Lemma asymmetric_erase : forall B x g R,
  erase (open_tm_wrt_tm B (a_Var_f x)) R =
  erase (open_tm_wrt_tm B (a_Conv (a_Var_f x) R g)) R.
Proof.
  intros.
  rewrite <- open_tm_erase_tm.
  rewrite <- open_tm_erase_tm.
  simpl.
  destruct R; eauto.
Qed.




(* ------- contexts ---------------------- *)

Lemma erase_dom : forall G R, dom G = dom (erase_context G R).
Proof.
  induction G. simpl. auto.
  intro. destruct a. simpl. rewrite (IHG R). eauto.
Qed.


(* value_type *)


Lemma CoercedValueValue_erase:
  (forall R v,  CoercedValue R v -> CoercedValue R (erase v R)) /\
  (forall R v, Value R v -> Value R (erase v R)).
Proof. apply CoercedValue_Value_mutual; eauto.
  all: intros.
  all: try destruct rho.
  all: try match goal with [H : lc_tm (?a ?b) |- _ ] =>
                           apply lc_tm_erase with (R := R) in H; simpl in * end.
  all: simpl; autorewcs; eauto using lc_tm_erase, lc_constraint_erase.

  destruct R1, R; auto. simpl. eapply CC; auto.
  all: try solve [econstructor; intros x Fr;
  replace (a_Var_f x) with (erase (a_Var_f x) R); auto;
  rewrite open_tm_erase_tm; eauto].
Qed.

Lemma Value_erase :  (forall R v, Value R v -> Value R (erase v R)).
Proof. eapply CoercedValueValue_erase. Qed.

Lemma CoercedValue_erase :  (forall R v, CoercedValue R v -> CoercedValue R (erase v R)).
Proof. eapply CoercedValueValue_erase. Qed.

Lemma value_type_erase: forall R a, value_type R a -> value_type R (erase a R).
Proof.
  intros R a H2.
  induction H2; simpl in *; lc_inversion c; subst; eauto with lc.
  all : econstructor; eauto with lc.
Qed.

(* ---------------------------------- *)

Lemma ann_rho_swap : forall rho x x0 a R,
    x `notin` fv_tm_tm_tm (erase_tm a R) ->
    x0 `notin` fv_tm_tm_tm (erase_tm a R) ->
    RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x)) R) ->
    RhoCheck rho x0 (erase_tm (open_tm_wrt_tm a (a_Var_f x0)) R).
Proof.
  intros rho x x0 a R F1 F2 H0.
  inversion H0; subst; constructor.
  + auto.
  + autorewcs. rewrite -open_tm_erase_tm. simpl.
    autorewcshyp H. rewrite -open_tm_erase_tm in H. simpl in H.
    eapply fv_swap with (x:=x); eauto.
Qed.

(* --------------------------------------------------------- *)

(* Simplify an expression with erase/open_tm or erase/close_tm *)
Ltac simpl_erase :=
  simpl;
  repeat match goal with
         | [ |- context [ erase (open_tm_wrt_tm ?a ?b) ?R ] ] =>
           autorewcs; rewrite -open_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase_tm (open_tm_wrt_tm ?a ?b) ?R ] ] =>
           autorewcs; rewrite -open_tm_erase_tm; simpl; autorewcs

         | [ |- context [ erase (close_tm_wrt_tm ?x ?a) ?R ] ] =>
           autorewcs; rewrite -close_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase_tm (close_tm_wrt_tm ?x ?a) ?R ] ] =>
           autorewcs; rewrite -close_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase (close_tm ?x ?a) ?R ] ] =>
           autorewcs; rewrite -close_tm_erase_tm; simpl; autorewcs

         | [ |- context [ erase (tm_subst_tm_tm ?a ?x ?b) ?R ] ] =>
           autorewcs; rewrite -subst_tm_erase_tm; simpl; autorewcs
         | [ |- context [ erase_tm (tm_subst_tm_tm ?a ?x ?b) ?R ] ] =>
           autorewcs; rewrite -subst_tm_erase_tm; simpl; autorewcs


end.

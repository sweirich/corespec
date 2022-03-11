(* Parameterization of the grade lattice *)

Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.
Require Import ssreflect.

Module Type GradeSig.

Parameter grade : Set. 

Parameter q_Top : grade.
Parameter q_Bot : grade.
Parameter q_C   : grade.

Parameter q_R   : grade.

Parameter q_eqb  : grade -> grade -> bool.
Parameter q_leb  : grade -> grade -> bool.
Parameter q_join : grade -> grade -> grade.
Parameter q_meet : grade -> grade -> grade. 

Parameter q_eq   : grade -> grade.

(* Equality *)
Definition t := grade.
Definition eq := @Logic.eq grade.
Definition eqb  := q_eqb.
Parameter q_eq_dec : forall (A : grade) (B : grade), { A = B } + { not (A = B) }.
Instance equ  : @EqDec_eq grade := q_eq_dec. 
Parameter eqb_eq : forall (n m : grade), q_eqb n m = true <-> n = m.
Definition eq_equiv : Equivalence (@Logic.eq grade) := eq_equivalence.
Definition eq_dec := q_eq_dec.
Include BackportEq.

(* Order *)
Definition leb  := q_leb.
Definition le n m := is_true (q_leb n m).
Definition q_lt n m := is_true (q_leb n m) /\ n <> m. 

(* Size *)
Definition size_grade : grade -> nat := fun _ => 1%nat.
Lemma size_grade_min : forall q1, (1 <= size_grade q1). intros. unfold size_grade. auto. Qed.

(* Notation *)
Declare Scope grade_scope.
Bind Scope grade_scope with grade.
Local Open Scope grade_scope.

Infix "=?" := q_eqb (at level 70) : grade_scope.
Infix "<=?" := q_leb (at level 70) : grade_scope.
Notation "q1 <= q2" := (is_true (q_leb q1 q2)) (at level 70)  : grade_scope.
Notation "q1 < q2" := (q_lt q1 q2) (at level 70)  : grade_scope.
Notation "x * y"  := (q_join x y) : grade_scope.  
Notation "x + y " := (q_meet x y)  : grade_scope.

(* join and meet are commutative and associative *)
Axiom join_assoc : forall a b c, a * (b * c) = (a * b) * c.
Axiom join_comm  : forall a b, a * b = b * a.
Axiom meet_assoc : forall a b c, a + (b + c) = (a + b) + c.
Axiom meet_comm : forall a b, a + b = b + a.

(* absorption laws *)
Axiom absorb_meet : forall a b, a * (a + b) = a.
Axiom absorb_join : forall a b, a + (a * b) = a.

(* join and meet are idempotent *)
Axiom join_idem : forall a, a * a = a.
Axiom meet_idem : forall psi, psi + psi = psi.

(* bounded *)
Axiom join_Top_r : forall a, a * q_Top = q_Top.
Axiom meet_Bot_r : forall a, a + q_Bot = q_Bot.

Axiom C_lt_Top : q_C < q_Top.

Axiom R_lt_C : q_R < q_C.

(* Everything is either below or above C, and you can tell which *)
Axiom order_q_C_dec : forall q, { q <= q_C } + { q_C < q }.

(* Pre order *)
Axiom leb_leq  : forall (n m : grade), (n <=? m) = true <-> n <= m.

Axiom join_leq : forall a b,  a <= b -> (a * b) = b.
Axiom leq_join : forall a b, (a * b) = b -> a <= b.

Axiom meet_leq : forall a b,  a <= b -> (a + b) = a.
Axiom leq_meet : forall a b, (a + b) = a -> a <= b.

Lemma q_leb_refl : forall n, is_true (n <=? n).
Proof. intro n. apply leq_join. rewrite join_idem. auto. Qed.

Lemma q_leb_trans: forall m n p, is_true (n <=? m) -> is_true (m <=? p) -> is_true (n <=? p).
Proof. intros. apply leq_join. apply join_leq in H. apply join_leq in H0. rewrite <- H0.
rewrite join_assoc. rewrite -> H. auto. Qed.

Instance le_preorder : PreOrder le.
Proof. split. intro x. apply q_leb_refl. unfold Transitive. intros. eapply q_leb_trans; eauto. Qed.


End GradeSig.

Declare Module Grade : GradeSig.
Export Grade.

Hint Rewrite join_assoc join_Top_r join_idem : grade. 

Section GradeFacts.

(* Properties about the lattice used in the development. *)

Local Open Scope grade_scope.

Lemma q_leb_antisym : forall a b, a <= b -> b <= a -> a = b.
Proof. intros. apply join_leq in H. apply join_leq in H0. rewrite join_comm in H0.
rewrite <- H. symmetry. auto. Qed.

Lemma leq_Top : forall a, a <= q_Top. 
Proof. intros. apply leq_join. rewrite join_Top_r. auto. Qed.

Lemma leq_Bot : forall a, q_Bot <= a. 
Proof. intros. apply leq_meet. rewrite meet_comm. rewrite meet_Bot_r. auto. Qed.

Lemma leq_join_l : forall a b, a <= a * b.
Proof. intros. apply leq_join. rewrite join_assoc. rewrite join_idem. auto. Qed.

Lemma leq_join_r : forall a b, b <= a * b.
Proof. intros. apply leq_join. rewrite join_comm. rewrite <- join_assoc. rewrite join_idem. auto. Qed.

Lemma join_Top_l : forall a, q_Top * a = q_Top. 
Proof. intros. rewrite join_comm. apply join_Top_r. Qed.

Lemma join_idem_l : forall (a b:grade), a * (a * b) = a * b.
Proof. intros. rewrite join_assoc. rewrite join_idem. auto. Qed.

Hint Rewrite join_idem_l join_Top_l : grade.

Lemma po_join_l : forall a b c , a <= b -> a * c <= b * c.
Proof. intros. apply leq_join. apply join_leq in H.
rewrite join_assoc.
replace (a * c * b * c) with (a * (c * b) * c). 2: autorewrite with grade; auto.
rewrite (join_comm c). autorewrite with grade.
rewrite <- join_assoc. rewrite join_idem.
rewrite H. auto. Qed.

Lemma po_join_r : forall a b c , a <= b -> c * a <= c * b.
Proof. 
  intros. apply leq_join. apply join_leq in H.
  rewrite (join_comm c a). rewrite join_assoc.
  replace (a * c * c * b) with (a * (c * c) * b). rewrite join_idem.
  rewrite <- join_assoc. rewrite (join_comm c b). rewrite join_assoc.
  rewrite H. auto. 
  rewrite join_assoc. auto.
Qed.

Lemma join_lub : forall a b c, 
    a <= c -> b <= c -> a * b <= c.
Proof. 
  intros. apply leq_join. apply join_leq in H. apply join_leq in H0.
  rewrite <- join_assoc. rewrite H0. auto. Qed.

Lemma leq_meet_l : forall a b, a + b <= a.
Proof. intros. apply leq_meet. rewrite (meet_comm a b). 
       rewrite <- meet_assoc.
       rewrite meet_idem. auto. Qed.

Lemma leq_meet_r : forall a b, a + b <= b.
Proof. intros. apply leq_meet.
       rewrite <- meet_assoc. rewrite meet_idem. auto. Qed.

Lemma po_meet_l : forall a b c , a <= b -> a + c <= b + c.
Proof. 
  intros. apply leq_meet. apply meet_leq in H.
  rewrite meet_assoc. 
  replace (a + c + b + c) with (a + (c + b) + c).
  rewrite (meet_comm c b). rewrite meet_assoc.
  rewrite H. rewrite <- meet_assoc. rewrite meet_idem. auto.
  rewrite meet_assoc. auto.
Qed.

Lemma po_meet_r : forall a b c , a <= b -> c + a <= c + b.
Proof. intros. rewrite meet_comm. rewrite (meet_comm c b).
       apply po_meet_l. auto. Qed.


Lemma still_higher : forall a b,
  q_C < a -> b <= q_C -> q_C < a * b.
Proof.
  intros. inversion H. 
  apply join_leq in H0. apply join_leq in H1. 
  split. 
  - apply leq_join. 
    rewrite join_assoc. rewrite H1. auto.
  - move => h. apply H2. apply q_leb_antisym. apply leq_join. auto.
    apply leq_join.
    rewrite <- H0. rewrite join_assoc. rewrite <- h. rewrite join_idem. 
    symmetry. auto.
Qed.

Lemma meet_mult : forall {a b}, 
      a <= q_C -> 
      q_C + (b * a) = (q_C + b) * a.
Proof.
  intros.
  destruct (order_q_C_dec b).
  + move: (meet_leq _ _ i) => h1. rewrite meet_comm in h1. rewrite h1.
    have LT: (a * b <= q_C). apply join_lub; auto.
    rewrite meet_comm. 
    move: (meet_leq _ _ LT) => h2. rewrite join_comm in h2. rewrite h2.
    rewrite join_comm. auto.
  + inversion q. clear q. clear H1.
    move: (meet_leq _ _ H0) => h1. rewrite h1.
    have LT: (q_C <= a * b).
    transitivity (a * q_C). eapply leq_join_r. eapply po_join_r. auto.
    apply meet_leq in LT. rewrite join_comm in LT. rewrite LT.
    apply join_leq in H. rewrite <- H at 1. rewrite join_comm. auto.
Qed.

Lemma lt_not_leq : forall {psi psi0},
 psi < psi0 -> ~ psi0 <= psi.
Proof.
  intros psi psi0 H. inversion H. move=>h. apply H1. eapply q_leb_antisym; auto. Qed.

Lemma not_leq_lower : forall {psi psi0 phi},
    psi <= phi -> ~ psi0 <= phi -> ~ psi0 <= psi.
Proof.
  intros. move=> h. apply H0. transitivity psi; auto. 
Qed.
 
End GradeFacts.



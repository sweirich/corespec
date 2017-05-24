Require Import FcEtt.imports.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Definition first :=
  fun (A B C D  E: Prop) (p : A /\ B /\ C /\ D /\ E) =>
    match p with
      | conj H _ => H
    end.
Definition second :=
  fun (A B C D E : Prop) (p : A /\ B /\ C /\ D /\ E) =>
    match p with
      | conj _ (conj H _) => H
    end.
Definition third :=
  fun (A B C D E : Prop) (p : A /\ B /\ C /\ D /\ E) =>
    match p with
      | conj _ (conj _ (conj H _)) => H
    end.
Definition fourth :=
  fun (A B C D E : Prop) (p : A /\ B /\ C /\ D /\ E) =>
    match p with
      | conj _ (conj _ (conj _ (conj H _))) => H
    end.
Definition fifth :=
  fun (A B C D E : Prop) (p : A /\ B /\ C /\ D /\ E) =>
    match p with
      | conj _ (conj _ (conj _ (conj _ H))) => H
    end.


(* ------------------------------------- *)

Lemma dom_subst_inv: forall (G: context) (f: sort -> sort), dom G = dom (map f G).
Proof.
  induction G; eauto.
  intros f.
  destruct a.
  simpl.
  rewrite (IHG f); auto.
Qed.

(* -------------------------------------- *)

Lemma binds_map_3 :
   forall a b x s (f : a -> b) G, binds x s (map f G) ->
    exists s', f s' = s /\ binds x s' G.
intros. induction G. simpl in H. inversion H.
destruct a0 as [x0 s0].
simpl in H.
apply binds_cons_iff in H. destruct H. destruct H. subst.
exists s0. auto.
apply IHG in H. destruct H as [s' [ EQ B]].
exists s'. auto.
Qed.

(* -------------------------------------- *)

Lemma binds_cases: forall G F x A y B,
    uniq (F ++ [(y, B)] ++ G) ->
    @binds sort x A (F ++ [(y, B)] ++ G) ->
    (binds x A F /\ x <> y /\ x `notin` dom G) \/ (x = y /\ A = B) \/ (binds x A G /\ x <> y /\ x `notin` dom F).
Proof.
  intros G F x A y B U b.
  edestruct binds_app_1. eauto 1.
  + left. split.
    auto.
    move: (fresh_app_r _ x A _ F U H) => Fr.
    simpl in Fr.
    split. eauto. eauto.
  + edestruct binds_app_1. eauto 1.
    right. left. apply binds_one_iff. auto.
  - right. right.
    move: (uniq_app_2 _ _ _ U) => U1.
    move: (fresh_app_l _ x A _ _ U1 H0) => Fr.
    simpl in Fr.
    repeat split; eauto.
    eapply fresh_app_l; eauto 1.
Qed.

(* ------------------------------------- *)


Lemma binds_concat: forall G F E x A, binds x (Tm A) (F ++ E ++ G) <-> binds x (Tm A) (F) \/ binds x (Tm A) (E) \/ binds x (Tm A) (G).
Proof.
  intros G F E x A.
  split.
  - intros H.
    induction F; eauto.
    induction E; eauto.
    simpl in H.
    case H; eauto.
    move => h0.
    fsetdec.
    move => h0.
    right.
    simpl in IHE.
    case:IHE; try done.
    move => h1.
    case:h1; eauto.
    move => h1.
    left.
    right; auto.
    case H; auto.
    fsetdec.
    move => h0.
    case IHF; try done.
    move => h1.
    left.
    right; auto.
    move => h1.
    case: h1; auto.
  - induction F; eauto.
    induction E; eauto.
    simpl.
    move => h1.
    case:h1; try done.
    move => h1.
    case:h1; try done.
    move => h1.
    case:h1; try done.
    move => h1.
    case h1; eauto.
    move => h0.
    case h0.
    move => h1.
    case:h1.
    fsetdec.
    move => h1.
    right.
    apply IHF; eauto.
    move => h1.
    right.
    apply IHF; eauto.
Qed.


(* ------------------------------------- *)

Lemma fun_cong : forall A B (f : A -> B) (a b : A),  a = b -> f a = f b.
Proof.
  intros. f_equal. eauto.
Qed.

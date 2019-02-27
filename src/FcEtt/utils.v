Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Definition map := EnvImpl.map.

(**** Auxiliary definitions ****)


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

Lemma fun_cong : forall A B (f : A -> B) (a b : A),  a = b -> f a = f b.
Proof.
  intros. f_equal. eauto.
Qed.


(* ------------------------------------- *)

(* Lemmas that should be part of metalib *)

Lemma dom_subst_inv: forall (G: context) (f: sort -> sort), dom G = dom (map f G).
Proof.
  induction G; eauto.
  intros f.
  destruct a.
  simpl.
  rewrite (IHG f); auto.
Qed.


Lemma utils_map_map : forall A B C (f : B -> C) (g: A -> B) (G:list(atom*A)),
  map f (map g G) = map (fun x => f (g x)) G.
Proof.
  induction G. simpl. auto.
  simpl. destruct a. f_equal. auto.
Qed.




Definition domFresh {a} (sub:list (atom * a)) s :=
  Forall (fun '(x,_) => x `notin` s) sub.

Lemma domFresh_empty : forall A (G:list(atom*A)), domFresh G empty.
Proof. 
  induction G; unfold domFresh in *; try destruct a; eauto.
Qed.

Lemma domFresh_singleton : forall A (G:list(atom*A)) x, 
   domFresh G (singleton x) <-> x `notin` dom G.
Proof.
  induction G; intros; unfold domFresh. 
  simpl. split. auto. intro. auto.
  destruct a. simpl. 
  split. intro h; inversion h. subst.
  apply IHG in H2. fsetdec.
  intro. econstructor; eauto. eapply IHG. fsetdec.
Qed.

Lemma domFresh_singleton2 : forall A (G:list(atom*A)) x, 
   x `notin` dom G ->
   domFresh G (singleton x).
Proof.
  intros.
  erewrite domFresh_singleton.
  auto.
Qed.

Lemma domFresh_cons : forall A x (st:A) Gp s,
 domFresh (x ~ st ++ Gp) s <-> 
 x `notin` s /\ (domFresh Gp s).
Proof. 
  intros.
  unfold domFresh in *.  
  split. intro h. inversion h. auto.
  intros [h0 h1].
  econstructor; eauto.
Qed.

Lemma domFresh_cons1 : forall A x (st:A) Gp s,
 domFresh (x ~ st ++ Gp) s -> 
 x `notin` s /\ (domFresh Gp s).
Proof.
  intros.
  rewrite -> domFresh_cons in H.
  auto.
Qed.

Lemma domFresh_union : forall (G:list (atom*sort)) s1 s2,
 domFresh G (s1 `union` s2) <-> 
 domFresh G s1 /\ (domFresh G s2).
Proof.
  induction G; intros; unfold domFresh in *. split; eauto.
  split; move=>h; inversion h; destruct a; simpl.
  rewrite -> IHG in H2. split_hyp.
  split; econstructor; try fsetdec; eauto.
  inversion H. inversion H0.
  econstructor; eauto 1.
  rewrite IHG. eauto.
Qed.

Lemma domFresh_union1 : forall (G:list (atom*sort)) s1 s2,
 domFresh G (s1 `union` s2) -> 
 domFresh G s1 /\ (domFresh G s2).
Proof.
  intros.
  rewrite -> domFresh_union in H.
  auto.
Qed.

Lemma domFresh_sub : forall A (G:list(atom*A)) s1 s2, 
    s1 [<=] s2 -> domFresh G s2 -> domFresh G s1.
Proof. 
  induction G; unfold domFresh; simpl.
  intros; auto.
  intros.
  inversion H0. destruct a.
  econstructor; eauto.
  eapply IHG; eauto.
Qed.



Lemma dom_zip_map_fst : forall D C (G:list(atom*D)) (x:list C),
  length G = length x ->
  dom (zip (List.map fst G) x) [=] dom G.
Proof. 
  induction G; intros; simpl; auto. reflexivity.
  simpl in H. inversion H.
  destruct x. destruct a. 
  inversion H.
  destruct a. simpl. rewrite IHG. fsetdec. auto.
Qed.

Lemma domFresh_map_fst_eq : forall A (G1: list(atom*A)) B (G2:list(atom*B)) s, 
    (List.map fst G1) = (List.map fst G2) -> 
    domFresh G1 s -> domFresh G2 s.
Proof.   
  induction G1;
  intros; unfold domFresh in *; destruct G2; inversion H; inversion H0;  simpl.
  auto.
  econstructor; eauto.
  destruct a. destruct p. simpl in *. subst. auto.
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

Lemma binds_concat: forall G F E x A, 
    binds x (Tm A) (F ++ E ++ G) 
    <-> binds x (Tm A) (F) \/ binds x (Tm A) (E) \/ binds x (Tm A) (G).
Proof.
  intros G F E x A.
  split.
  - intros H.
    apply binds_app_1 in H.
    destruct H; auto.
    apply binds_app_1 in H.
    destruct H; auto.
  - intros.
    destruct H.
    eauto.
    destruct H.
    auto.
    auto.
Qed.



(* ------------------------------------- *)

(* Facts about NoDup *)

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

Lemma dom_rev : forall A (l : list (atom * A)) x, x `in` dom l ->
                                                  x `in` dom (rev l).
Proof. intros. induction l; eauto.
       destruct a. simpl in H. simpl. rewrite dom_app. simpl.
       fsetdec.
Qed.

Lemma uniq_rev : forall A (l : list (atom * A)), uniq l -> uniq (rev l).
Proof. intros. induction H; simpl; eauto. apply uniq_reorder_1.
       simpl. econstructor. auto. intro. apply H0. apply dom_rev in H1.
       rewrite rev_involutive in H1. auto.
Qed.

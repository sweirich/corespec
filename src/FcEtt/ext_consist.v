
Require Import FcEtt.sigs.

Require Import Lia.

Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ett_par.
Require Export FcEtt.erase_syntax.
Require Import FcEtt.ext_red_one.
Require Import FcEtt.ext_red.

Require Import FcEtt.ext_wf.
Import FcEtt.ett_par.

Module ext_consist (invert : ext_invert_sig)(fc_wf: fc_wf_sig).
Import invert.
Import fc_wf.

Module red_one := ext_red_one invert.
Export red_one.

Module red := ext_red invert.
Export red.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


Fixpoint interp_constraint (G : context) (D : available_props) (phi : constraint) : Prop :=
  match phi with
  | Eq A B1 T1 => exists C, multipar G D A C /\ multipar G D B1 C
  | Impl phi1 phi2 => interp_constraint G D phi1 -> interp_constraint G D phi2
  end.

Definition Good (G : context) (D : available_props):=
  erased_context G /\
  forall c1 phi,
    binds c1 (Co phi) G
    -> c1 `in` D
    -> interp_constraint G D phi.

(* ---------------------------------------- *)

Lemma open2 :
  forall x b b' S D a a',
    x `notin` fv_tm_tm_tm a' \u fv_tm_tm_tm a ->
    erased_tm b ->
    erased_tm (open_tm_wrt_tm a (a_Var_f x)) ->
    Par S D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)) ->
    Par S D b b' ->
    Par S D (open_tm_wrt_tm a b) (open_tm_wrt_tm a' b').
Proof.
  intros x b b'. intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ b')] (tm_subst_tm_tm_intro x); auto.
  apply subst3; auto.
Qed.

Lemma open2_constraint :
  forall x b b' S D phi phi',
    x `notin` fv_tm_tm_constraint phi' \u fv_tm_tm_constraint phi ->
    erased_tm b ->
    erased_constraint (open_constraint_wrt_tm phi (a_Var_f x)) ->
    ParProp S D (open_constraint_wrt_tm phi (a_Var_f x)) (open_constraint_wrt_tm phi' (a_Var_f x)) ->
    Par S D b b' ->
    ParProp S D (open_constraint_wrt_tm phi b) (open_constraint_wrt_tm phi' b').
Proof.
  intros x b b'. intros.
  rewrite (tm_subst_tm_constraint_intro x); auto.
  rewrite [(_ _ b')] (tm_subst_tm_constraint_intro x); auto.
  apply subst3; auto.
Qed.


Lemma a_Pi_head : forall S G b A rho B,
    Par S G (a_Pi rho A B) b -> exists A' B' L,
      b = a_Pi rho A' B' /\ Par S G A A' /\
      (forall x, x `notin` L -> Par S G (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x))).
Proof.
  intros. inversion H. subst. inversion H0.  exists A , B, empty. split; auto.
  subst.
  exists A', B', L.  split; auto.
Qed.

Lemma Par_Abs_inversion : forall G D a b rho,
    Par G D (a_UAbs rho a) b ->
    (exists a', b = (a_UAbs rho a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' ->
               Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)))
    \/
    (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' rho (a_Var_f x)) /\ rho = Rel)
    \/ (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' rho a_Bullet) /\ rho = Irrel). 

Proof.
  intros G D a a' rho P.
  inversion P; subst.
  + left. exists a. inversion H; eauto.
  + left. exists a'0. split. auto.
    intros x Fr.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite (tm_subst_tm_tm_intro y a'0); eauto.
    apply subst2; eauto.
  + right. left. 
    exists b. split. auto.
    split; eauto.
    intros x Fr.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite H5; eauto.
    simpl.
    rewrite tm_subst_tm_tm_fresh_eq; auto.
    destruct eq_dec. auto.
    done. 
  + right. right.
    exists b. split. auto.
    split; eauto.
    intros x Fr.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite H5; eauto.
    simpl.
    rewrite tm_subst_tm_tm_fresh_eq; auto. 
Qed.

Lemma Par_Abs_inversion_Rel : forall G D a b,
    Par G D (a_UAbs Rel a) b ->
    (exists a', b = (a_UAbs Rel a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' ->
               Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)))
    \/
    (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' Rel (a_Var_f x))).
Proof.
  intros G D a b H. eapply Par_Abs_inversion in H. inversion H; eauto.
  inversion H0; eauto.
  - right. inversion H1. inversion H2. inversion H4. eauto.
  - inversion H1. inversion H2. inversion H4. inversion H6.
Qed. 

Lemma Par_Abs_inversion_Irrel : forall G D a b,
    Par G D (a_UAbs Irrel a) b ->
    (exists a', b = (a_UAbs Irrel a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' ->
               Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)))
    \/ (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' Irrel a_Bullet)). 
Proof.
  intros G D a b H. eapply Par_Abs_inversion in H. inversion H; eauto.
  inversion H0; eauto.
  - right. inversion H1. inversion H2. inversion H4. inversion H6.
  - right. inversion H1. inversion H2. inversion H4. eauto.
Qed.


(*
Lemma Par_Abs_inversion_Irrel_2: forall G D a b,
    Par G D (a_UAbs Irrel a) b ->
    (exists a', b = (a_UAbs Irrel a') /\
               Par G D (open_tm_wrt_tm a (a_Bullet)) (open_tm_wrt_tm a' (a_Bullet)))
    \/ (exists a', Par G D a' b /\ (forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' Irrel a_Bullet)). 
Proof. 
  intros G D a b H. eapply Par_Abs_inversion in H. inversion H; eauto.
  inversion H0; eauto.
  - right. inversion H1. inversion H2. inversion H4. inversion H6.
  - right. inversion H1. inversion H2. inversion H4. eauto.
Qed. *)


Lemma Par_CAbs_inversion : forall G D a b,
    Par G D (a_UCAbs a) b ->
    (exists a', b = (a_UCAbs a') /\
          forall c, c `notin` fv_co_co_tm a \u fv_co_co_tm a' ->
               Par G D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)))
    \/ (exists a', Par G D a' b /\ (forall c, c `notin`  fv_co_co_tm a ->
          open_tm_wrt_co a (g_Var_f c) = a_CApp a' g_Triv)). 
Proof.
  intros G D a b H. inversion H; subst.
  - left. exists a. inversion H0; eauto.
  - left. exists a'. split. auto.
    intros c Fr. 
    pick fresh y.
    rewrite (co_subst_co_tm_intro y); eauto.
    rewrite (co_subst_co_tm_intro y a'); eauto.
    apply subst4; eauto.
  - right. exists b0. split; auto.
    intros c Fr. pick fresh y. 
    rewrite (co_subst_co_tm_intro y); eauto.
    rewrite H4; eauto. simpl. 
    rewrite co_subst_co_tm_fresh_eq; auto.
Qed.


Lemma copen2 :
  forall c (b: co) S D a a',
    lc_co b ->
    c `notin` fv_co_co_tm a' \u fv_co_co_tm a ->
    Par S D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)) ->
    Par S D (open_tm_wrt_co a b) (open_tm_wrt_co a' b).
Proof.
  intros x b b'. intros.
  rewrite (co_subst_co_tm_intro x); auto.
  rewrite [(_ _ b)] (co_subst_co_tm_intro x); auto.
  apply subst4; auto.
Qed.

Lemma copen2_constraint :
  forall c (b: co) S D phi phi',
    lc_co b ->
    c `notin` fv_co_co_constraint phi' \u fv_co_co_constraint phi ->
    ParProp S D (open_constraint_wrt_co phi (g_Var_f c)) (open_constraint_wrt_co phi' (g_Var_f c)) ->
    ParProp S D (open_constraint_wrt_co phi b) (open_constraint_wrt_co phi' b).
Proof.
  intros x b b'. intros.
  rewrite (co_subst_co_constraint_intro x); auto.
  rewrite [(_ _ b)] (co_subst_co_constraint_intro x); auto.
  apply subst4; auto.
Qed.


(* -------------------------------------------------------------------------------- *)

Ltac try_refl :=
  try match goal with
      | [ P2 : Par _ _ _ ?b |- _ ] =>
        exists b; assert (lc_tm b); try eapply Par_lc2; eauto; try split; eauto; fail
      (* I don't know what the tactic does exactly, but here's the
      ParProp case that I think makes sense *)
      | [ P2 : ParProp _ _ _ ?phi |- _ ] =>
        exists phi; assert (lc_constraint phi); try eapply Par_lc2; eauto; try split; eauto; fail
      end.

(*
Ltac invert_syntactic_equality :=
  match goal with
      | [ H : a_UAbs _ _ = a_UAbs _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_Pi _ _ _ = a_Pi _ _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_UCAbs _ = a_UCAbs _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_App _ _ _ = _ _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_CApp _ _  = a_CApp _ _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_Fam _ = a_Fam _ |- _ ] =>
        inversion H; subst; clear H
      | [ H : a_CPi _ _ = a_CPi _ _ |- _ ] =>
        inversion H; subst; clear H
  end.
*)
Ltac invert_equality :=
  match goal with
  | [ H : _ = _ |- _ ] =>
    inversion H
  end.

  Ltac try_refl_left :=
  try match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?b cc /\ Par ?S ?D ?a2 cc ] =>
        exists a2; assert (lc_tm a2); try eapply Par_lc2; eauto; try split; eauto; fail
      | [ P2 : ParProp _ _ ?phi ?phi |- exists cc:constraint, ParProp ?S ?D ?phi cc /\ Par ?S ?D ?phi' cc ] =>
        exists phi'; assert (lc_constraint phi'); try eapply Par_lc2; eauto; try split; eauto; fail
      end.
  Ltac try_refl_right :=
  try match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?a2 cc /\ Par ?S ?D ?b cc ] =>
        exists a2; assert (lc_tm a2); try eapply Par_lc2; try eapply Par_lc1_tm; eauto; try split; eauto; fail
      | [ P2 : ParProp _ _ ?b ?b |- exists cc:constraint, ParProp ?S ?D ?a2 cc /\ ParProp ?S ?D ?b cc ] =>
        exists a2; assert (lc_constraint a2); try eapply Par_lc2; try eapply Par_lc2_tm; eauto; try split; eauto; fail
      end.

  Ltac invert_erased :=
    match goal with
    | [ H : erased_tm ?a |- _ ] => inversion H; subst; clear H
    | [ H : erased_constraint ?a |- _ ] => inversion H; subst; clear H
    end.

  (* Find prove that the result of Par is erased, and then invert that *)
  Ltac invert_erased_tm b :=
        let h0 := fresh in
        match goal with
          [ h : Par ?G ?D ?a b, h1: erased_tm ?a |- _ ] =>
          assert (h0 : erased_tm b);
          [ eapply (Par_erased_tm h); eauto | inversion h0; subst]
        end.


        (*    If we know that (a ^ x) == (App b rho x), replace
             (a ^ b0) with (App b rho b0)
            The tactic only succeeds if there is only 1 equality in
            the context.
       *)
      Ltac eta_expand x :=
        let h1 := fresh in
      match goal with
       | [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_tm ?a (a_Var_f x) = a_App ?b0 ?rho (a_Var_f x)
              |- _ ] =>
        pick fresh x for (L0 \u  fv_tm_tm_tm a \u fv_tm_tm_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@tm_subst_tm_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite tm_subst_tm_tm_fresh_eq; auto
       | [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_tm ?a (a_Var_f x) = a_App ?b0 ?rho a_Bullet
              |- _ ] =>
        pick fresh x for (L0 \u  fv_tm_tm_tm a \u fv_tm_tm_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@tm_subst_tm_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite tm_subst_tm_tm_fresh_eq; auto
       | [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_co ?a (g_Var_f x) = a_CApp ?b0 g_Triv
              |- _ ] =>
        pick fresh x for (L0 \u  fv_co_co_tm a \u fv_co_co_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@co_subst_co_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite co_subst_co_tm_fresh_eq; auto
      end.


       (* Rewrite a goal of the form
            ... (a'0 ^ b'0) ...
          To
            ... (b . b'0) ...
          and try to solve it, give eta-assn Y2 *)
      Ltac eta_case a'0 Y2 :=
         let x:= fresh in
         pick fresh x;
         rewrite (tm_subst_tm_tm_intro x a'0); auto;
         rewrite Y2; auto; simpl;
         rewrite (tm_subst_tm_tm_fresh_eq); auto;
         destruct eq_dec; try done;
         eauto; clear x.



Ltac invert_lc :=
  match goal with
    | [ H : lc_tm ?a |- _ ] => inversion H; subst; clear H
    | [ H : lc_constraint ?a |- _ ] => inversion H; subst; clear H
  end.

  Ltac use_size_induction a ac Par1 Par2 :=
  match goal with
  | [   IH : forall y: nat, (* ?T1 -> forall t:tm, *) ?T,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H : Par ?G ?D a ?b0,
        H4 : Par ?G ?D a ?b1 |- _ ] =>
      move: (@IH (size_tm a) ltac:(lia) a ltac:(auto) _ _ _ H2 H3 H _ H4) => [ ac [Par1 Par2]]
  | [   IH : forall y: nat, (* ?T1 -> forall phi:constraint, *) ?T,
        H2 : Good ?G ?D,
        H3 : erased_constraint a,
        H : ParProp ?G ?D a ?b0,
        H4 : ParProp ?G ?D a ?b1 |- _ ] =>
      move: (@IH (size_constraint a) ltac:(lia) a ltac:(auto) _ _ _ H2 H3 H _ H4) => [ ac [Par1 Par2]]
  end.


  Ltac use_size_induction_open a0 x ac Par1 Par2 :=
      let h0 := fresh in
      let h1 := fresh in
      let h2 := fresh in
      let EQ1 := fresh in
      let EQ2 := fresh in
      match goal with
        | [  H : ∀ x : atom,
              x `notin` ?L
              → Par ?S ?D (?open_tm_wrt_tm a0 (?a_Var_f x)) ?b,
             H4: ∀ x : atom,
                 x `notin` ?L0
                 → Par ?S ?D (?open_tm_wrt_tm a0 (?a_Var_f x)) ?c,
             H1 : ∀ x : atom, x `notin` ?L1 →
    erased_tm (?open_tm_wrt_tm a0 (?a_Var_f x)) |- _ ] =>
    move: (H x ltac:(auto)) => h0; clear H;
    move: (H4 x ltac:(auto)) => h1; clear H4;
                               move: (H1 x ltac:(auto)) => h2; clear H1;
    move: (size_tm_open_tm_wrt_tm_var a0 x) => EQ1;
    move: (size_tm_open_tm_wrt_co_var a0 x) => EQ2;

    use_size_induction (open_tm_wrt_tm a0 (a_Var_f x)) ac Par1 Par2;
    clear h0; clear h1; clear h2; clear EQ1; clear EQ2
    end.

(*
Ltac use_induction a ac Par1 Par2 :=
  match goal with
  | [ IHPar1 : Good ?G ?D -> erased_tm a → ∀ a2 : tm, Par ?G ?D ?a a2 → ?T ,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H4 : Par ?G ?D a ?b |- _ ] =>
    destruct (IHPar1 H2 H3 _ H4) as [ac [Par1 Par2]]
  end.

Ltac use_induction_on a b ac Par1 Par2 :=
  match goal with
  | [ IHPar1 : Good ?G ?D -> erased_tm a → ∀ a2 : tm, Par ?G ?D ?a a2 → ?T ,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H4 : Par ?G ?D a b |- _ ] =>
    destruct (IHPar1 H2 H3 _ H4) as [ac [Par1 Par2]]
  end.
*)

Ltac par_erased_open x J Par4 :=
  let K := fresh in
  let KK := fresh in
  let h0 := fresh in
  match goal with
  | [H13 : ∀ x : atom, x `notin` ?L →
                       Par ?G ?D (open_tm_wrt_tm ?a (a_Var_f x)) ?b,
     H4 : ∀ x : atom, x `notin` ?L1 → erased_tm  (open_tm_wrt_tm ?a (a_Var_f x))
       |- _ ] =>
    have: x `notin` L; auto => h0;
    pose K:= H13 x h0; clearbody K; clear h0;
    have: x `notin` L1; auto => h0;
    pose KK := H4 x h0; clearbody KK;
    pose J := subst3_tm x Par4 KK K;
    clearbody J;
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in J; [auto;
    simpl in J;
    destruct eq_dec; try congruence;
    repeat rewrite tm_subst_tm_tm_fresh_eq in J; auto
    | try apply (Par_lc2_tm Par4); auto
    | apply (Par_lc1_tm Par4); auto]
  end.

Ltac finish_open_co a'0 :=
  let K := fresh in
  let J := fresh in
  let h0 := fresh in
  match goal with
  | H12 : forall c, c `notin` ?L -> Par ?G ?D (open_tm_wrt_co a'0 (g_Var_f c)) (open_tm_wrt_co ?b (g_Var_f c)) |- _ =>
      pick_fresh c;
      have: c `notin` L; auto => h0;
                                pose K := H12 c h0; clearbody K;
                                          pose J := subst4 c lc_g_Triv K;
                                                    clearbody J;
                                                    repeat rewrite co_subst_co_tm_open_tm_wrt_co in J; eauto;
                                                    simpl in J;
                                                    destruct eq_dec; try congruence;
                                                    repeat rewrite co_subst_co_tm_fresh_eq in J; eauto with lc

  end.


Lemma open_tm_wrt_tm_bullet_var_eq: forall a x, 
    x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x)) ->
    open_tm_wrt_tm a (a_Bullet) = open_tm_wrt_tm a (a_Var_f x).
Proof.
  intros.  
  rewrite (tm_subst_tm_tm_intro x a a_Bullet); auto.
  rewrite tm_subst_tm_tm_fresh_eq. auto.
  auto.
  rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower.
  eauto.
Qed.


Lemma open_tm_wrt_tm_inj_irrel: forall(a2 a1 : tm) (x1 : atom),
x1 `notin` fv_tm_tm_tm (open_tm_wrt_tm a2 (a_Var_f x1)) 
-> x1 `notin` fv_tm_tm_tm (open_tm_wrt_tm a1 (a_Var_f x1))
  -> open_tm_wrt_tm a2 a_Bullet = open_tm_wrt_tm a1 (a_Var_f x1)
    -> a2 = a1.
Proof. 
  intros. erewrite open_tm_wrt_tm_bullet_var_eq in H1; eauto.
  eapply open_tm_wrt_tm_inj; eauto. rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. 
  rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto. 
Qed.

Lemma open_tm_wrt_co_triv_var_eq: forall a c, 
    c `notin` fv_co_co_tm (open_tm_wrt_co a (g_Var_f c)) ->
    open_tm_wrt_co a g_Triv = open_tm_wrt_co a (g_Var_f c).
Proof.
  intros.  
  rewrite (co_subst_co_tm_intro c a g_Triv); auto.
  rewrite co_subst_co_tm_fresh_eq. auto.
  auto.
  rewrite fv_co_co_tm_open_tm_wrt_co_lower.
  eauto.
Qed.

Lemma open_tm_wrt_co_inj: forall(a2 a1 : tm) (c : atom),
c `notin` fv_co_co_tm (open_tm_wrt_co a2 (g_Var_f c)) 
-> c `notin` fv_co_co_tm (open_tm_wrt_co a1 (g_Var_f c))
  -> open_tm_wrt_co a2 g_Triv = open_tm_wrt_co a1 (g_Var_f c)
    -> a2 = a1.
Proof.
  intros. erewrite open_tm_wrt_co_triv_var_eq in H1; eauto.
  eapply open_tm_wrt_co_inj; eauto. rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto. 
  rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto.
Qed.

Lemma erased_fv_co: forall x, (forall a, erased_tm a -> x `notin` fv_co_co_tm a) /\
                           (forall phi, erased_constraint phi -> x `notin` fv_co_co_constraint phi).
Proof.
  intros x.
  apply erased_tm_constraint_mutual; intros. all: simpl. all: try fsetdec.
  - pick fresh y. move: (H y ltac:(auto)) =>  h1.
    rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto.
  - pick fresh y. move: (H0 y ltac:(auto)) => h1.
    apply union_notin_iff. split; eauto.
    rewrite fv_co_co_tm_open_tm_wrt_tm_lower. eauto.
  - pick fresh y. move: (H0 y ltac:(auto)) => h1.
    apply union_notin_iff. split. clear Fr. fsetdec.
    rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto.
  - pick fresh y. move: (H y ltac:(auto)) =>  h1.
    rewrite fv_co_co_tm_open_tm_wrt_co_lower. eauto.
Qed.

(* Lemma confluence_size : forall n a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b. *)
(* Proof. *)
(*   pose confluence_size_def n := *)
(*       forall a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b. *)

Lemma confluence_size : forall n,
  ((forall a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b) /\ 
    (forall phi, size_constraint phi <= n -> forall S D phi1, Good S D -> erased_constraint phi -> ParProp S D phi phi1 ->
      forall phi2, ParProp S D phi phi2 -> exists phi3, ParProp S D phi1 phi3 /\ ParProp S D phi2 phi3)).
Proof.
  pose confluence_size_def n :=
    ((forall a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b) /\ 
       (forall phi, size_constraint phi <= n -> forall S D phi1, Good S D -> erased_constraint phi -> ParProp S D phi phi1 ->
                                                     forall phi2, ParProp S D phi phi2 -> exists phi3, ParProp S D phi1 phi3 /\ ParProp S D phi2 phi3)).
  intro n. fold (confluence_size_def n).  eapply (well_founded_induction_type lt_wf).
  clear n. intros n IH. unfold confluence_size_def in *. clear confluence_size_def.
  assert (∀ y : nat,
         y < n
         → (∀ a : tm,
              size_tm a ≤ y
              → ∀ (S : context) (D : available_props) (a1 : tm),
                  Good S D
                  → erased_tm a
                    → Par S D a a1
                      → ∀ a2 : tm,
                          Par S D a a2
                          → ∃ b : tm, Par S D a1 b ∧ Par S D a2 b)) as IHtm.
  apply IH.
  intros.
  assert (∀ y : nat,
         y < n
         → (∀ phi : constraint,
                size_constraint phi ≤ y
                → ∀ (S : context) (D : available_props) (phi1 : constraint),
                    Good S D
                    -> erased_constraint phi
                    → ParProp S D phi phi1
                      → ∀ phi2 : constraint,
                          ParProp S D phi phi2
                          → ∃ phi3 : constraint,
                              ParProp S D phi1 phi3 ∧ ParProp S D phi2 phi3)) as IHconstraint.
  apply IH.
  split.
  intros a SZ S D a1 Gs Ea P1 a2 P2.
  - inversion P1; inversion P2; subst.
  all: try solve [invert_equality].
  (* 37 subgoals *)
  all: try_refl_left.
  all: try_refl_right.
  all: try invert_syntactic_equality.
  all: simpl in SZ; destruct n; try solve [ inversion SZ ].
  all: invert_erased; inversion Gs.
    -- (* two rel betas *)
      use_size_induction a0 ac Par1 Par2.
      use_size_induction b bc Par3 Par4.
      destruct (Par_Abs_inversion_Rel Par1) as [[a'' [EQ h0]] | [X1]]; subst;
        destruct (Par_Abs_inversion_Rel Par2) as [[a''' [EQ2 h1]]| [Y1]]; subst.
    --- inversion EQ2. subst.
       exists (open_tm_wrt_tm a''' bc).
       split. pick fresh x; eapply open2; eauto using Par_erased_tm.
       pick fresh x; eapply open2; eauto using Par_erased_tm.
    --- exists (open_tm_wrt_tm a'' bc).
       split. pick fresh x; eapply open2; eauto using Par_erased_tm.
       inversion H7.
       eta_expand x.
    --- exists (open_tm_wrt_tm a''' bc).
       split. inversion H7. eta_expand x. 
       pick fresh x; eapply open2; eauto using Par_erased_tm.
    --- exists (a_App ac Rel bc).
       split. inversion H7. eta_expand x0.
       inversion H8. eta_expand x0.
    -- (* rel app beta / app cong *)
      use_size_induction a0 ac Par1 Par2.
      use_size_induction b bc Par3 Par4.
      invert_erased_tm (a_UAbs Rel a').
      inversion Par1; subst; clear Par1.
      --- exists (open_tm_wrt_tm a' bc); auto.
          split; eauto.
          apply open1 with (L:=L); eauto.
      --- exists (open_tm_wrt_tm a'1 bc); auto.
          split; eauto.
          pick_fresh x.
          par_erased_open x J Par3.
      --- exists (a_App ac Rel bc).
          split.
          eta_expand x. 
          eauto.
  -- (* two irrel betas *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UAbs Irrel a');
    invert_erased_tm (a_UAbs Irrel a'0).
    destruct (Par_Abs_inversion_Irrel Par1) as [ [a'' [EQ X]] | W ];
    destruct (Par_Abs_inversion_Irrel Par2) as [ [a''' [EQ' X']] | W'].
    * subst.
      exists (open_tm_wrt_tm a''' a_Bullet).
      split; eauto. 
      pick fresh x; eapply open2; eauto. inversion EQ'; subst.
      apply X. fsetdec. 
      pick fresh x; eapply open2; eauto.
    * subst. 
      exists (open_tm_wrt_tm a'' a_Bullet). 
      split. pick fresh x; eapply open2; eauto.
      destruct W' as [ax [Par5 K]].
      eta_expand x.
    * exists (open_tm_wrt_tm a''' a_Bullet). split. 
      destruct W as [ax [Par5 K]]. 
      inversion EQ'; subst. eta_expand x. 
      pick fresh x; eapply open2; eauto.
    * exists (a_App ac Irrel a_Bullet). split.
      destruct W as [ax [Par5 K]].
      eta_expand x. destruct W' as [z [Par5 K]].
      eta_expand x.
  (* Irrel app beta / app cong *)
   -- use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UAbs Irrel a').
    inversion Par1; subst; clear Par1.
    --- exists (open_tm_wrt_tm a' a_Bullet); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    --- exists (open_tm_wrt_tm a'1 a_Bullet); auto.
      split; eauto.
      pick_fresh x; eapply open2; eauto.
    --- exists (a_App ac Irrel a_Bullet).
      split. eta_expand x. 
      eauto.
   (* rel app cong / app beta *)
  -- use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    invert_erased_tm (a_UAbs Rel a'0).
    inversion Par2; subst; clear Par2.
    --- exists (open_tm_wrt_tm a'0 bc); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    --- exists (open_tm_wrt_tm a'1 bc); auto.
      split; eauto.
      pick_fresh x.
      par_erased_open x J Par4.
    --- exists (a_App ac Rel bc).
      split. eauto.
      eta_expand x.
  -- (* rel app cong / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    exists (a_App ac Rel bc).
    split. eauto. eauto.
  -- (* Irrel app cong / app beta *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UAbs Irrel a'0).
    inversion Par2; subst; clear Par2.
    --- exists (open_tm_wrt_tm a'0 a_Bullet); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    --- exists (open_tm_wrt_tm a'1 a_Bullet); auto.
      split; eauto. pick_fresh x; eapply open2; eauto.
    --- exists (a_App ac Irrel a_Bullet).
      split. eauto.
      eta_expand x.
  -- (* Irrel app cong / app cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_App ac Irrel a_Bullet).
    split. eauto. eauto.
  -- (* two cbetas *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UCAbs a').
    invert_erased_tm (a_UCAbs a'0).
    destruct (Par_CAbs_inversion Par1) as [ [a'' [EQ X]] | W ];
    destruct (Par_CAbs_inversion Par2) as [ [a''' [EQ' X']] | W']. 
    --- subst.
      exists (open_tm_wrt_co a''' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
      inversion EQ'; subst.
      apply X. fsetdec.
      pick fresh x; eapply copen2; eauto.
    --- subst. 
      exists (open_tm_wrt_co a'' g_Triv). 
      split. pick fresh x; eapply copen2; eauto.
      destruct W' as [ax [Par5 K]].
      eta_expand c.
    --- exists (open_tm_wrt_co a''' g_Triv). split. 
      destruct W as [ax [Par5 K]]. 
      inversion EQ'; subst. eta_expand c. 
      pick fresh x; eapply copen2; eauto.
    --- exists (a_CApp ac g_Triv). split.
      destruct W as [ax [Par5 K]].
      eta_expand c. destruct W' as [z [Par5 K]].
      eta_expand c.
  -- (* cbeta / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    destruct (Par_CAbs_inversion Par1) as [ [a'' [EQ X]] | W ].
    inversion P2; subst; clear P2.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
      rewrite H7. eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. pick fresh x; eapply copen2; eauto.
    + exists (a_CApp ac g_Triv). split; eauto.
      destruct W as [ax [Par5 K]]. eta_expand c.
  -- (* capp cong / cbeta *)
    use_size_induction a0 ac Par1 Par2.
    destruct (Par_CAbs_inversion Par2) as [ [a'' [EQ X]] | W ].
    inversion P2; subst; eauto; clear P2.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. rewrite H3. pick fresh x; eapply copen2; eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. rewrite H7. pick fresh x; eapply copen2; eauto.
    + exists (open_tm_wrt_co a'' g_Triv).
      split; eauto. rewrite H7. pick fresh x; eapply copen2; eauto.
    + exists (a_CApp ac g_Triv). split; eauto.
      destruct W as [ax [Par5 K]]. eta_expand c.
  -- (* capp cong / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_CApp ac g_Triv). auto.
  -- (* abs cong / abs cong *)
    pick fresh x.
    use_size_induction_open a0 x ac Par1 Par2.
    exists (a_UAbs rho (close_tm_wrt_tm x ac)).
    split; eauto; try solve [apply (@Par_Abs_exists x); eauto].
  -- (* abs cong rel / eta rel *)
    pick fresh x.
    move: (H x ltac:(auto)) => h1. clear H. rewrite H5 in h1.
    (* h1 : b x => a' *)
    inversion h1.
    + subst. (* refl b x => b x *)
      exists a2. split.
            pick fresh y and apply Par_Eta; eauto.
      apply eta_swap with (x:=x); eauto.
      eauto using Par_lc2_tm.
    + subst. (* b x => a' ^ x  where b => \a' *)
      inversion H11. subst.
      apply open_tm_wrt_tm_inj in H9; auto. subst. 
      move: (H5 x ltac:(auto)) => h2.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h2; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      assert (size_tm b <= size_tm a0). lia.
      move: (H2 x ltac:(auto)) => h4. rewrite h2 in h4. inversion h4.
      use_size_induction b bb Par1 Par2.
      exists bb. eauto.
      eapply Par_fv_preservation in H10. simpl in H10. eauto. eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H9 in h1.
      inversion H11. subst. clear H11.
      move: (H5 x ltac:(auto)) =>  h2.
      move: (H2 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). lia.
      use_size_induction b bb Par1 Par2.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ H10 ltac:(eauto)) => h5.
      exists bb.
      split.
      pick fresh y and apply Par_Eta. eapply Par2.
      eapply eta_swap with (x:=x); eauto.
      eauto.
    + eauto.
  -- (* abs cong irrel / eta irrel *)
    pick fresh x. move: (H3 x ltac:(auto)) => h5. inversion h5; subst.
    move: (H x ltac:(auto)) => h1. rewrite H5 in h1.
    (* h1 : b x => a' *)
    inversion h1.
    + subst. (* refl b x => b x *)
      exists a2. split.
            pick fresh y and apply Par_EtaIrrel; eauto.
      apply eta_swap_irrel with (x:=x); eauto.
      eauto using Par_lc2_tm.
    + subst.
      move: (H2 x ltac:(auto)) => k1.
      rewrite H5 in k1.
      inversion k1.
      assert (erased_tm (a_UAbs Irrel a'0)). eapply Par_erased_tm. eauto. auto.
      eapply erased_a_Abs_inversion in H9.
      inversion H9; clear H9.
      assert (x `notin` fv_tm_tm_tm (open_tm_wrt_tm a'0 (a_Var_f x))).
      inversion H13; eauto.
      apply open_tm_wrt_tm_inj_irrel in H10; subst.
      move: (H5 x ltac:(auto)) => h2.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h2; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      assert (size_tm b <= size_tm a0). lia.
      move: (H2 x ltac:(auto)) => h4. rewrite h2 in h4. inversion h4.
      use_size_induction b bb Par1 Par2.
      exists bb. split; eauto. auto.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ h1 ltac:(eauto)) => h6. eauto.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ H11 ltac:(eauto)) => h7. eauto.
      (*helping fsetdec a bit*) apply union_notin_iff in Fr. fsetdec.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H10 in h1.
      move: (H5 x ltac:(auto)) =>  h2.
      move: (H2 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). lia.
      use_size_induction b bb Par1 Par2.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ h1 ltac:(eauto)) => h6.
      exists bb.
      split. 
      pick fresh y and apply Par_EtaIrrel. eapply Par2.
      eapply eta_swap_irrel with (x:=x); eauto.
      eapply Par_erased_tm in h1; eauto. simpl in h6.
      (*helping fsetdec a bit*) apply union_notin_iff in Fr.
      inversion Fr. clear Fr.  clear Fr0. fsetdec.
      eauto.
    + eauto.
  -- (* pi cong / pi cong *)
    pick fresh x.
    use_size_induction A ac Par1 Par2.
    use_size_induction_open B x bc Par3 Par4.
    exists (a_Pi rho ac (close_tm_wrt_tm x bc)).
    split; eauto; try solve [apply (@Par_Pi_exists x); eauto].
  -- (* cabs cong / cabs cong *)
    pick fresh c.
    use_size_induction_open a0 c ac Par1 Par2.
    exists (a_UCAbs (close_tm_wrt_co c ac)).
    split; eauto; try solve [apply (@Par_CAbs_exists c); eauto].
  -- (* cabs / eta c *)
    pick fresh x.
    move: (H x ltac:(auto)) => h1. clear H. rewrite H5 in h1.
    (* h1 : b x => a' *)
    inversion h1.
    + subst. (* refl b x => b x *)
      exists a2. split.
            pick fresh y and apply Par_EtaC; eauto.
      apply eta_swap_c with (x:=x); eauto.
      eauto using Par_lc2_tm.
    + subst.
      move: (H5 x ltac:(auto)) => h2.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h2; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_co_var in h3.
      assert (size_tm b <= size_tm a0). lia.
      move: (H1 x ltac:(auto)) => h4. rewrite h2 in h4. inversion h4.
      use_size_induction b bb Par1 Par2.
      exists bb. 
      split; eauto.
      eapply open_tm_wrt_co_inj in H7. subst; auto.
      Focus 2. move: (proj1 (Par_fv_co_preservation x) _ _ _ _ h1 ltac:(eauto)) => h5. eauto.
      apply erased_fv_co. eapply erased_a_CAbs_inversion.
      move: (@Par_erased_tm _ _ _ _ H8 ltac:(eauto)) => h6; eauto.
      move: (proj1 (Par_fv_co_preservation x) _ _ _ _ H8 ltac:(eauto)) => h5. 
      simpl in h5; eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H7 in h1.
      (*inversion H8. subst. clear H10.*)
      move: (H5 x ltac:(auto)) =>  h2.
      move: (H1 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_CApp ?b ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_CApp b x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_co_var in h4.
      assert (size_tm b <= size_tm a0). lia.
      use_size_induction b bb Par1 Par2.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ H8 ltac:(eauto)) => h5.
      exists bb.
      split; eauto.
      pick fresh y and apply Par_EtaC; eauto.
      eapply eta_swap_c with (x:=x); eauto. clear Fr0.
      move: (proj1 (Par_fv_co_preservation x) _ _ _ _ h1 ltac:(eauto)) => h6.
      simpl in h6. rewrite union_notin_iff. split. 
      apply union_notin_iff in Fr. inversion Fr. clear Fr. fsetdec.
      clear Fr. fsetdec.
    + eauto.
  -- (* cpi cong / cpi cong *)
    use_size_induction phi phiC Par1 Par2.
    pick fresh c.
    use_size_induction_open a0 c ac Par7 Par8.
    exists (a_CPi phiC (close_tm_wrt_co c ac)).
    split; eauto; try solve [apply (@Par_CPi_exists c); eauto].
  -- (* fam / fam *)
    have E: (Ax a1 A = Ax a2 A0). eapply binds_unique; eauto using uniq_toplevel.
    inversion E. subst. clear E.
    have LC: lc_tm a2. apply Toplevel_lc in H. inversion H. auto.
    exists a2. split; eauto.
  -- (* eta rel / abs cong rel *)
    pick fresh x.
    match goal with
      [ H5 : ∀ x : atom,
            x `notin` ?L0
            → Par ?S ?D (open_tm_wrt_tm ?a0 (a_Var_f x))
                  (open_tm_wrt_tm ?a' (a_Var_f x)),
        H :  ∀ x : atom,
            x `notin` ?L → open_tm_wrt_tm ?a0 (a_Var_f x) = a_App ?b ?rho (a_Var_f x)
            |- _ ] =>
      move: (H x ltac:(auto)) => h0;
      move: (H5 x ltac:(auto)) => h1; clear H5; rewrite h0 in h1
    end.
  (* h1 : b x => a' x *)
    inversion h1; subst.
    + exists a1. split. eauto using Par_lc2_tm.
       pick fresh y and apply Par_Eta; eauto.
       apply eta_swap with (x:=x); eauto.
    + (* b x => a' ^ x  where b => \a' *)
      match goal with
        [  H8 : Par ?S ?D ?b (a_UAbs ?rho ?a'0),
          H11 : Par ?S ?D (a_Var_f x) ?b',
          H10 : open_tm_wrt_tm a'0 ?b' = open_tm_wrt_tm ?a' (a_Var_f x)
          |- _ ] =>
        inversion H11; subst;
          move: (proj1 (Par_fv_preservation x) S D _ _ H8 ltac:(auto)) => h2; simpl in h2; eauto;
          apply open_tm_wrt_tm_inj in H10; auto; subst; clear H11
      end.
      match goal with
        [ H : ?a = ?b |- _ ] =>
        assert (h3 : size_tm a = size_tm b) end.
      rewrite h0; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      assert (size_tm b <= size_tm a0). lia.
      let h4 := fresh in
      match goal with
        [ H2 :  ∀ x : atom, x `notin` ?L1 → erased_tm (open_tm_wrt_tm ?a0 (a_Var_f x)) |- _ ] =>
        move: (H2 x ltac:(auto)) => h4; rewrite h0 in h4; inversion h4; subst
      end.
      use_size_induction b bb Par1 Par2.
      exists bb. eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H9 in h1.
      inversion H11. subst. clear H11.
      move: (H0 x ltac:(auto)) =>  h2.
      move: (H3 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). lia.
      use_size_induction b bb Par1 Par2.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ H10 ltac:(eauto)) => h5.
      exists bb.
      split.
      eauto.
      pick fresh y and apply Par_Eta. eapply Par2.
      eapply eta_swap with (x:=x); eauto.
  -- (* eta rel / eta rel *)
    pick fresh x for (L \u L0 \u L1).
    move: (H0 x ltac:(auto)) => E1.
    move: (H6 x ltac:(auto)) => E2.
    move: (H3 x ltac:(auto)) => Eb.
    rewrite E2 in E1.
    inversion E1. subst.
    rewrite E2 in Eb. inversion Eb. subst.
    move: (size_tm_open_tm_wrt_tm_var a0 x) => Sb.
    match goal with
      [ H : open_tm_wrt_tm ?a ?x = ?b |- _ ] =>
      assert (K : size_tm (open_tm_wrt_tm a x) = size_tm b);
        [rewrite H; auto| simpl in K]
    end.
    use_size_induction b ac Par1 Par2.
    exists ac. auto.
  -- (* eta irrel / abs cong irrel*)
    pick fresh x.
    match goal with
      [ H5 : ∀ x : atom,
            x `notin` ?L0
            → Par ?S ?D (open_tm_wrt_tm ?a0 (a_Var_f x))
                  (open_tm_wrt_tm ?a' (a_Var_f x)),
        H :  ∀ x : atom,
            x `notin` ?L → open_tm_wrt_tm ?a0 (a_Var_f x) = a_App ?b ?rho a_Bullet
            |- _ ] =>
      move: (H x ltac:(auto)) => h0;
      move: (H5 x ltac:(auto)) => h1; clear H5; rewrite h0 in h1
    end.
  (* h1 : b x => a' x *)
    inversion h1; subst.
    + exists a1. split. eauto using Par_lc2_tm.
       pick fresh y and apply Par_EtaIrrel; eauto.
       apply eta_swap_irrel with (x:=x); eauto.
    + (* b x => a' ^ x  where b => \a' *)
      assert (h3: size_tm (open_tm_wrt_tm a0 (a_Var_f x)) 
              = size_tm (a_App b Irrel a_Bullet)). rewrite h0; auto.
      rewrite size_tm_open_tm_wrt_tm_var in h3.
      simpl in h3.
      assert (size_tm b <= size_tm a0). lia.
      let h4 := fresh in
      match goal with
        [ H2 :  ∀ x : atom, x `notin` ?L1 → erased_tm (open_tm_wrt_tm ?a0 (a_Var_f x)) |- _ ] =>
        move: (H2 x ltac:(auto)) => h4; rewrite h0 in h4; inversion h4; subst
      end.
      use_size_induction b bb Par1 Par2.
      exists bb. split; eauto.
      apply open_tm_wrt_tm_inj_irrel in H8; subst; eauto.
      Focus 2. move: (proj1 (Par_fv_preservation x) _ _ _ _ h1 ltac:(eauto)) => h5.
      auto.
      assert (erased_tm (a_UAbs Irrel a'0)). eapply Par_erased_tm. eauto. auto.
      eapply erased_a_Abs_inversion in H7.
      inversion H7; clear H7.
      assert (x `notin` fv_tm_tm_tm (open_tm_wrt_tm a'0 (a_Var_f x))).
      inversion H12; eauto. auto.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ H9 ltac:(eauto)) => h6.
      simpl in h6. auto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H8 in h1.
      move: (H0 x ltac:(auto)) =>  h2.
      move: (H3 x ltac:(auto)) => h3.
      rewrite h2 in h3. inversion h3. subst.
      match goal with
        [ H : ?a = a_App ?b ?rho ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_App b rho x)) end.
      rewrite h2; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_tm_var in h4.
      assert (size_tm b <= size_tm a0). lia.
      use_size_induction b bb Par1 Par2.
      exists bb.
      split.
      eauto.
      pick fresh y and apply Par_EtaIrrel. eapply Par2.
      eapply eta_swap_irrel with (x:=x); eauto.
      move: (proj1 (Par_fv_preservation x) _ _ _ _ h1 ltac:(eauto)) => h5.
      simpl in h5. clear Fr0. apply union_notin_iff in Fr. 
      inversion Fr. rewrite union_notin_iff. split; auto.
  -- (* eta irrel / eta irrel *) 
    pick fresh x for (L \u L0 \u L1).
    move: (H0 x ltac:(auto)) => E1.
    move: (H6 x ltac:(auto)) => E2.
    move: (H3 x ltac:(auto)) => Eb.
    rewrite E2 in E1.
    inversion E1. subst.
    rewrite E2 in Eb. inversion Eb. subst.
    move: (size_tm_open_tm_wrt_tm_var a0 x) => Sb.
    match goal with
      [ H : open_tm_wrt_tm ?a ?x = ?b |- _ ] =>
      assert (K : size_tm (open_tm_wrt_tm a x) = size_tm b);
        [rewrite H; auto| simpl in K]
    end.
    use_size_induction b ac Par1 Par2.
    exists ac. auto.
  -- (* eta c / cabs *)
    pick fresh x.
    match goal with
      [ H5 : ∀ c : atom,
            c `notin` ?L0
            → Par ?S ?D (open_tm_wrt_co ?a0 (g_Var_f c))
                  (open_tm_wrt_co ?a' (g_Var_f c)),
        H :  ∀ c : atom,
            c `notin` ?L → open_tm_wrt_co ?a0 (g_Var_f c) = a_CApp ?b g_Triv
            |- _ ] =>
      move: (H x ltac:(auto)) => h0;
      move: (H5 x ltac:(auto)) => h1; clear H5; rewrite h0 in h1
    end.
  (* h1 : b x => a' x *)
    inversion h1; subst.
    + exists a1. split. eauto using Par_lc2_tm.
       pick fresh y and apply Par_EtaC; eauto.
       apply eta_swap_c with (x:=x); eauto.
    + (* b x => a' ^ x  where b => \a' *)
      subst.
      move: (H2 x ltac:(auto)) => h2.
      assert (h3 : size_tm (open_tm_wrt_co a0 (g_Var_f x)) = size_tm (a_CApp b g_Triv)).
      rewrite h0; auto.
      simpl in h3.
      rewrite size_tm_open_tm_wrt_co_var in h3.
      assert (size_tm b <= size_tm a0). lia.
      move: (H0 x ltac:(auto)) => h4. rewrite h4 in h2. inversion h2.
      use_size_induction b bb Par1 Par2.
      exists bb. 
      split; eauto.
      eapply open_tm_wrt_co_inj in H7. subst; auto.
      Focus 2. move: (proj1 (Par_fv_co_preservation x) _ _ _ _ h1 ltac:(eauto)) => h5. eauto.
      apply erased_fv_co. eapply erased_a_CAbs_inversion.
      move: (@Par_erased_tm _ _ _ _ H8 ltac:(eauto)) => h6; eauto.
      move: (proj1 (Par_fv_co_preservation x) _ _ _ _ H8 ltac:(eauto)) => h5. 
      simpl in h5; eauto.
    + subst. (* b x => a'0 x where b => a'0 *)
      rewrite -H7 in h1.
      (*inversion H8. subst. clear H10.*)
      move: (H2 x ltac:(auto)) =>  h2.
      move: (H0 x ltac:(auto)) => h3.
      rewrite h3 in h2. inversion h2. subst.
      match goal with
        [ H : ?a = a_CApp ?b ?x |- _ ] =>
        assert (h4 : size_tm a = size_tm (a_CApp b x)) end.
      rewrite h3; auto.
      simpl in h4.
      rewrite size_tm_open_tm_wrt_co_var in h4.
      assert (size_tm b <= size_tm a0). lia.
      use_size_induction b bb Par1 Par2.
      exists bb.
      split; eauto.
      pick fresh y and apply Par_EtaC; eauto.
      eapply eta_swap_c with (x:=x); eauto. clear Fr0.
      move: (proj1 (Par_fv_co_preservation x) _ _ _ _ h1 ltac:(eauto)) => h6.
      simpl in h6. rewrite union_notin_iff. split. 
      apply union_notin_iff in Fr. inversion Fr. clear Fr. fsetdec.
      clear Fr. fsetdec.
  -- (* eta c / eta c *)
    pick fresh x for (L \u L0 \u L1).
    move: (H0 x ltac:(auto)) => E1.
    move: (H6 x ltac:(auto)) => E2.
    move: (H2 x ltac:(auto)) => Eb.
    rewrite E2 in E1.
    inversion E1. subst.
    rewrite E2 in Eb. inversion Eb. subst.
    move: (size_tm_open_tm_wrt_co_var a0 x) => Sb.
    match goal with
      [ H : open_tm_wrt_co ?a ?x = ?b |- _ ] =>
      assert (K : size_tm (open_tm_wrt_co a x) = size_tm b);
        [rewrite H; auto| simpl in K]
    end. 
    use_size_induction b ac Par1 Par2.
    exists ac. auto.
  (* ParProp *)
  - intros.
    (* invert_equality removes the obviously conflicting cases *)
    inversion H2; inversion H3; subst; invert_equality; subst.
    + inversion H1; subst.
      simpl in H.
      use_size_induction a ac Par1 Par2.
      use_size_induction A AC Par3 Par4.
      use_size_induction b bc Par5 Par6.
      eauto.
    + simpl in H.
      inversion H1; subst.
      use_size_induction phi0 phi0c Par1 Par2.
      use_size_induction phi3 phi3c Par3 Par4.
      eauto.
Qed.


(* Extra tactic? There's the same one above confluenze size.

Ltac use_size_induction b ac Par1 Par2 :=
  match goal with
  | [   IH : forall y: nat, ?T,
        H2 : Good S D,
        H3 : erased_tm b,
        H : Par S D b ?b0,
        H4 : Par S D b ?b1 |- _ ] =>
      move: (@IH (size_tm b) ltac:(lia) b ltac:(auto) _ _ _ H2 H3 H _ H4) => [ ac [Par1 Par2]]
  end.
*)

Lemma confluence : forall S D a a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
Proof.
  intros.
  eapply confluence_size; eauto.
Qed.

Lemma confluence_prop : forall S D phi phi1, Good S D -> erased_constraint phi -> ParProp S D phi phi1 -> forall phi2, ParProp S D phi phi2 -> exists b, ParProp S D phi1 b /\ ParProp S D phi2 b.
Proof.
  intros.
  eapply confluence_size; eauto.
Qed.



(* ---------------------------------------------------------------------- *)

Lemma multipar_Star : forall S D A B, multipar S D A B -> A = a_Star -> B = a_Star.
Proof.
  intros S D A B H. induction H. auto.
  inversion H; intro K; auto; try inversion K.
Qed.

Lemma multipar_Bullet : forall S D B, multipar S D a_Bullet B -> B = a_Bullet.
Proof.
  intros S D B H. dependent induction H. auto.
  inversion H; auto; try inversion K.
Qed.

(* OLD
Inductive Path_consistent : const -> tm -> tm -> Prop :=
  PC_Const : forall T, Path_consistent T (a_Const T) (a_Const T)
| PC_App   : forall T a1 rho a2 b1 b2,
    erased_tm a2 -> erased_tm b2 ->
    Path_consistent T a1 b1 ->
    Path_consistent T (a_App a1 rho a2) (a_App b1 rho b2)
| PC_CApp  : forall T a1 b1,
    Path_consistent T a1 b1 ->
    Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv).
Hint Constructors Path_consistent. *)

(*
Inductive Path_consistent : const -> tm -> tm -> Prop :=
  PC_Const : forall T, Path_consistent T (a_Const T) (a_Const T)
| PC_App   : forall T a1 a2 b1 b2,
    erased_tm a2 -> erased_tm b2 ->
    Path_consistent T a1 b1 ->
    Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2)
| PC_AppIrrel : forall T a1 b1,
    Path_consistent T a1 b1 ->
    Path_consistent T (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet)
| PC_CApp  : forall T a1 b1,
    Path_consistent T a1 b1 ->
    Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv).
Hint Constructors Path_consistent.


Lemma Path_consistent_Path1 : forall T a b, Path_consistent T a b -> Path T a.
Proof. induction 1; eauto using erased_lc. Qed.
Lemma Path_consistent_Path2 : forall T a b, Path_consistent T a b -> Path T b.
Proof. induction 1; eauto using erased_lc. Qed.

Lemma Path_consistent_erased1 : forall T a b, Path_consistent T a b -> erased_tm a.
Proof. induction 1; eauto. Qed.
Lemma Path_consistent_erased2 : forall T a b, Path_consistent T a b -> erased_tm b.
Proof. induction 1; auto. Qed.
Hint Resolve Path_consistent_erased1 Path_consistent_erased2 : erased.

Lemma Path_consistent_Refl :
  forall a T, Path T a -> erased_tm a -> Path_consistent T a a.
Proof. induction 1; intro h; inversion h; auto. Qed.

Lemma Path_consistent_Trans_aux :
  forall b T,  Path T b -> forall a c, Path_consistent T a b -> Path_consistent T b c -> Path_consistent T a c.
Proof. induction 1.
       all: intros a0 c0 h1 h2.
       all: inversion h1; inversion h2; subst; auto.
    - inversion h1; inversion h2; subst; auto.
    - inversion h1; inversion h2; subst; auto.
Qed.

Lemma Path_consistent_Trans : forall T a b c,
  Path_consistent T a b -> Path_consistent T b c -> Path_consistent T a c.
Proof. intros. eapply Path_consistent_Trans_aux with (b:=b). eapply Path_consistent_Path2; auto.
       eauto. eauto. eauto.
Qed.


Lemma Path_consistent_Sym :
  forall T a b, Path_consistent T a b -> Path_consistent T b a.
Proof.
  induction 1; eauto.
Qed.

Lemma Par_Path_consistent :
  forall S D a b T, Par S D a b -> Path T a -> erased_tm a -> Path_consistent T a b.
Proof.
  induction 1; intros P E; inversion E; inversion P; subst; eauto with lc;
    eauto using Path_consistent_Refl with erased.
  - move: (IHPar1 H10 H3) => h0.
    inversion h0.
  - move: (IHPar H7 H1) => h0.
    inversion h0.
  - move: (IHPar H6 H1) => h0.
    inversion h0.
Qed.

Lemma multipar_Path_consistent :
  forall S D a b T, multipar S D a b -> Path T a -> erased_tm a -> Path_consistent T a b.
Proof.
  intros S D a b T H. induction H.
  eauto using Path_consistent_Refl.
  intros h0 e0.
  move: (Par_Path_consistent H h0 e0) => h1.
  eapply Path_consistent_Trans with (b:=b); eauto;
  eauto using Path_consistent_Path2 with erased.
Qed.


Lemma Par_Path :
  forall S D a b T, Par S D a b -> Path T a -> Path T b.
Proof.
  induction 1; intros P; inversion P; subst; eauto with lc.
  - move: (IHPar1 H6) => h0.
    inversion h0.
  - move: (IHPar H5) => h0.
    inversion h0.
  - move: (IHPar H4) => h0.
    inversion h0.
Qed.

Lemma multipar_Path : forall S D a b T ,
    multipar S D a b -> Path T a -> Path T b.
Proof.
  intros S D a b T H. induction H. induction 1; intros; eauto.
  intros. eauto using Par_Path.
Qed.


    Lemma Par_Path_consistent_App : forall T G D a1 a2 b1 b2,
        Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
        Par G D (a_App a1 Rel a2) ( a_App b1 Rel b2) ->
        Par G D a1 b1.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H9 (Path_consistent_Path1 H8) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.

    Lemma Par_Path_consistent_AppIrrel : forall T G D a1 b1,
        Path_consistent T (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet) ->
        Par G D (a_App a1 Irrel a_Bullet) ( a_App b1 Irrel a_Bullet) ->
        Par G D a1 b1.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H6 (Path_consistent_Path1 H4) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.

    Lemma Par_Path_consistent_CApp : forall T G D a1 b1,
        Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
        Par G D (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
        Par G D a1 b1.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H6 (Path_consistent_Path1 H4) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.

    Lemma Par_Path_consistent_App2 : forall T G D a1 a2 b1 b2,
        Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
        Par G D (a_App a1 Rel a2) (a_App b1 Rel b2) ->
        Par G D a2 b2.
    Proof.
      intros. inversion H. subst.
      inversion H0; subst.
      - lc_inversion c. auto.
      - move: (Par_Path_consistent H9 (Path_consistent_Path1 H8) ltac: (eauto with erased)) => h0.
        inversion h0.
      - auto.
    Qed.


    Lemma multipar_Path_consistent_App : forall G D a1 a2 b1 b2 T,
      multipar G D (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      multipar G D a1 b1.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_App h0 H) => h1.
        eapply mp_step with (b:= b0). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_App a1 Rel a2).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

    Lemma multipar_Path_consistent_AppIrrel : forall G D a1 b1 T,
      multipar G D (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet) ->
      Path_consistent T (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet) ->
      multipar G D a1 b1.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_AppIrrel h0 H) => h1.
        eapply mp_step with (b:= b0). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_App a1 Irrel a_Bullet).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

     Lemma multipar_Path_consistent_App2 : forall G D a1 a2 b1 b2 T,
      multipar G D (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      Path_consistent T (a_App a1 Rel a2) (a_App b1 Rel b2) ->
      multipar G D a2 b2.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_App2 h0 H) => h1.
        eapply mp_step with (b:= b3). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_App a1 Rel a2).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

    Lemma multipar_Path_consistent_CApp : forall G D a1 b1 T,
      multipar G D (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
      Path_consistent T (a_CApp a1 g_Triv) (a_CApp b1 g_Triv) ->
      multipar G D a1 b1.
    Proof.
      intros.
      dependent induction H.
      - eauto.
      - move: (Par_Path_consistent H (Path_consistent_Path1 H1) ltac:(eauto 2 with erased)) => h0.
        inversion h0. subst.
        move: (Par_Path_consistent_CApp h0 H) => h1.
        eapply mp_step with (b:= b0). auto.
        eapply IHmultipar; eauto 2.
        eapply Path_consistent_Trans with (b := a_CApp a1 g_Triv).
        eapply Path_consistent_Sym; auto.
        auto.
    Qed.

*)


Ltac binds_notbinds :=
    match goal with
    [ H0 : binds ?c (Ax ?T ?a) toplevel,
      H5 : forall (c : atom) a, not (binds c (Ax ?T a) an_toplevel) |- _  ] =>
      unfold not in H5; unfold toplevel in H0; unfold erase_sig in H0;
      apply binds_map_3 in H0; destruct H0 as (s' & EQ & B);
      destruct s'; simpl in EQ; inversion EQ; subst;
      apply H5 in B; contradiction
      end.

(*

Lemma Par_Const : forall S D T b,
    Par S D (a_Const T) b -> b = a_Const T.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma multipar_Const : forall S D T b,
    multipar S D (a_Const T) b ->
    (b = a_Const T).
Proof.
  intros S D T b H. dependent induction H; eauto using Par_Const.
Qed.
*)

Lemma multipar_Pi : forall S D rho A B, multipar S D A B -> forall A1 A2,
      A = a_Pi rho A1 A2 -> exists B1 B2, B = (a_Pi rho B1 B2).
intros S D rho A B H. induction H. intros. subst. exists A1, A2. auto.
intros. subst.
inversion H; subst; destruct (IHmultipar _ _ eq_refl) as [B1 [B2 EQ]]; auto;
exists B1, B2; auto.
Qed.

Lemma multipar_CPi : forall S D A C, multipar S D A C -> forall phi B, A = a_CPi phi B -> exists phi' C2,
        C = (a_CPi phi' C2).
Proof.
  intros S D A C H. induction H; intros; subst.
  exists phi. eauto.
  inversion H; subst; destruct (IHmultipar _ _ eq_refl) as [phi'' [C2 EQ]];
    eauto.
Qed.


Lemma multipar_UAbs_Rel : forall S D a b x,
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm b ->
    multipar S D (a_UAbs Rel a) b ->
    (exists b2, b = (a_UAbs Rel b2))
    \/ (exists a1, exists a2, multipar S D (a_UAbs Rel a) (a_UAbs Rel a1) /\
               open_tm_wrt_tm a1 (a_Var_f x) = a_App a2 Rel (a_Var_f x)).
Proof.
    intros S D a b x Fr H. dependent induction H.
    - left. exists a. auto.
    - rename b into c.
      rename a' into b.
      destruct (Par_Abs_inversion_Rel H); subst.
      + destruct H1 as [ a' [K W]]. rewrite K in H.
      assert (h0 : x `notin` fv_tm_tm_tm (a_UAbs Rel a')). eapply Par_fv_preservation; eauto.
      simpl in h0.
      destruct (IHmultipar a' ltac:(eauto)) as [ [b2 EQ2] | [a1 [a2 [mp1 F2]]] ]; subst; clear IHmultipar.
      auto. left. exists b2. auto. right. exists a1, a2. split. eauto. auto.
      + destruct H1 as [ a' [K W]]. right. exists a, a'. split; eauto using Par_lc1_tm.
Qed.

Lemma multipar_UAbs_Irrel : forall S D a b x,
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm b ->
    multipar S D (a_UAbs Irrel a) b ->
    (exists b2, b = (a_UAbs Irrel b2))
    \/ (exists a1, exists a2, multipar S D (a_UAbs Irrel a) (a_UAbs Irrel a1) /\
               open_tm_wrt_tm a1 (a_Var_f x) = a_App a2 Irrel a_Bullet).
Proof.
    intros S D a b x Fr H. dependent induction H.
    - left. exists a. auto.
    - rename b into c.
      rename a' into b.
      destruct (Par_Abs_inversion_Irrel H); subst.
      + destruct H1 as [ a' [K W]]. rewrite K in H.
      assert (h0 : x `notin` fv_tm_tm_tm (a_UAbs Rel a')). eapply Par_fv_preservation; eauto.
      simpl in h0.
      destruct (IHmultipar a' ltac:(eauto)) as [ [b2 EQ2] | [a1 [a2 [mp1 F2]]] ]; subst; clear IHmultipar.
      auto. left. exists b2. auto. right. exists a1, a2. split. eauto. auto.
      + destruct H1 as [ a' [K W]]. right. exists a, a'. split; eauto using Par_lc1_tm.
Qed.

Lemma multipar_CAbs : forall S D A C, multipar S D A C -> forall phi B, A = a_CAbs phi B -> exists phi' C2,
        C = (a_CAbs phi' C2).
Proof.
  intros S D A C H. induction H; intros; subst.
  exists phi, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ eq_refl) as [phi'' [C2 EQ]];
    eauto.
Qed.

(* --------------------------------------------------- *)

(*
Definition decide_Path : forall a, lc_tm a -> (exists T, Path T a) \/ (forall T, not (Path T a)).
Proof.
  induction a; intro lc.
  all: try solve [left; eauto].
  all: try solve [right; move => T h1; inversion h1].
  - lc_inversion c. destruct IHa1 as [[T h0]|n].
    auto.
    left; eauto.
    right. move => T h1. inversion h1.
    subst. unfold not in n. eauto.
  - lc_inversion c. destruct IHa as [[T h0]|n].
    auto.
    left; eauto.
    right. intros T h; inversion h; subst; unfold not in n; eauto.
  - lc_inversion c. destruct IHa as [[T h0]|n].
    auto.
    left. exists T. auto.
    right. intros T h; inversion h; subst; unfold not in n; eauto.
Qed. *)

(* --------------------------------------------------- *)


(* Proof that joinability implies consistency. *)

Ltac step_left := apply consistent_a_Step_R; [auto |intro N; inversion N; inversion H0]; fail.
Ltac step_right := apply consistent_a_Step_L; [auto | intro N; inversion N; inversion H0]; fail.

(* look for a multipar involvong a head form and apply the appropriate lemma for that
   head form. Note: for paths, the lemma has already been applied so we only need
   to look for a hypothesis about path consistency. *)
Ltac multipar_step SIDE EQ :=
  match goal with
  | [ SIDE : multipar _ _ a_Star _ |- _ ] =>
    apply multipar_Star in SIDE; auto; rename SIDE into EQ
  | [ SIDE : multipar _ _ (a_Pi _ _ _) _ |- _ ] =>
    destruct (multipar_Pi SIDE eq_refl) as [b1' [b2' EQ]]
  | [ SIDE : multipar _ _ (a_CPi ?phi _) _ |- _ ] =>
    try (destruct phi); destruct (multipar_CPi SIDE eq_refl)
      as (phi' & C2' &  EQ)
(*  | [ SIDE : multipar _ _ (a_Const ?T) _ |- _ ] =>
    apply multipar_Const in SIDE; auto; rename SIDE into EQ
  | [ SIDE : Path_consistent _ _ _ |- _ ] =>
    rename SIDE into EQ *)
  end.



Lemma join_consistent : forall S D a b, joins S D a b -> consistent a b.
Proof.
  intros.
  all: destruct H as (TT & Es & Ea & Eb & MSL & MSR).
  all: move: (erased_lc_tm Ea) => lc_a.
  all: move: (erased_lc_tm Eb) => lc_b.
  destruct a; try step_right; destruct b; try step_left; auto.
  (* 35 subgoals *)
  all: repeat
         let T  := fresh in
         let h0 := fresh in
         match goal with
           [ SIDE : multipar _ _ (a_App ?b1 ?rho ?b2) _,
               Eb : erased_tm (a_App ?b1 ?rho ?b2)  |- _ ] =>
           destruct (decide_Path (erased_lc Eb)) as [ [T h0] | NP ];
             [ eapply multipar_Path_consistent in SIDE; eauto | idtac ];
             clear Eb end.
    all: repeat
         let T  := fresh in
         let h0 := fresh in
         match goal with
           [ SIDE : multipar _ _ (a_CApp ?b1 ?b2) _, Eb: erased_tm (a_CApp ?b1 ?b2)  |- _ ] =>
           destruct (decide_Path (erased_lc Eb)) as [ [T h0] | NP ];
             [ eapply multipar_Path_consistent in SIDE; eauto | idtac ];
             clear Eb
         end.
  all: try solve [inversion Ea].
  all: try solve [inversion Eb].
  all: try solve [inversion Eb; inversion Ea; eauto].

  all: try multipar_step MSL EQ1.
  all: try multipar_step MSR EQ2.
  all: try solve [rewrite EQ1 in EQ2; inversion EQ2; try inversion H; auto using Par_lc_1_tm].
  all: try solve [eapply consistent_a_Step_R; [auto | intros h0; inversion h0; unfold not in NP; eauto using Par_lc1_tm]].
  all: try solve [eapply consistent_a_Step_L; [auto with lc | intros h0; inversion h0; unfold not in NP; eauto with lc]].
  - destruct (multipar_Pi MSL eq_refl) as (B1 & B2 & EQ).
    destruct (multipar_Pi MSR eq_refl) as (B1' & B2' & EQ').
    subst.
    inversion EQ. inversion EQ'.
    subst. econstructor; eauto.
    inversion lc_a. auto.
    inversion lc_b. auto.
  - destruct (multipar_CPi MSL eq_refl) as (B1 & B2 & EQ).
    destruct (multipar_CPi MSR eq_refl) as (B1'' & B2'' & EQ').
    subst.
    inversion EQ. inversion EQ'.
    subst. econstructor; eauto.
    inversion lc_a. auto.
    inversion lc_b. auto.
  - inversion Ea; inversion Eb; subst; constructor; auto with lc.
Qed.

(*

a  -> b -->* c      d - by confluence
|     |      |      e - by induction
v     v      v
a2 -> d -->* e
*)

Lemma multipar_confluence_helper : forall S D a a1, Good S D -> erased_tm a -> multipar S D a a1
-> forall a2, Par S D a a2 -> exists e, Par S D a1 e /\ multipar S D a2 e.
Proof.
  intros S D a a1 Es E H. induction H.
  - intros. exists a2. split; eauto with lc erased.
  - intros. destruct (confluence Es E H H1) as [d [L R]].
      inversion Es.
      assert (erased_tm b). eapply Par_erased_tm; eauto.
      destruct (IHmultipar Es H4 d L) as [e [LL RR]]; auto.
      exists e. split; eauto.
Qed.

Lemma multipar_prop_confluence_helper : forall S D phi phi1,
    Good S D -> erased_constraint phi -> multipar_prop S D phi phi1 ->
    forall phi2, ParProp S D phi phi2 -> exists phi3, ParProp S D phi1 phi3 /\ multipar_prop S D phi2 phi3.
Proof.
  intros S D phi phi1 Es E H. induction H.
  - intros. exists phi2. split; eauto with lc erased.
  - intros. destruct (confluence_prop Es E H H1) as [d [L R]].
      inversion Es.
      assert (erased_constraint phi2). eapply Par_erased_constraint; eauto.
      destruct (IHmultipar_prop Es H4 d L) as [e [LL RR]]; auto.
      exists e. split; eauto.
Qed.
(*

a -->  b -->* c    d - by prior lemma
|      |      |    e - by induction.
v      v      v
*      *      *
a2 --> d -->* e

*)


Lemma multipar_lc1: forall G D a1 a2, multipar G D a1 a2 -> lc_tm a1.
Proof.
  intros.
  inversion H; subst; auto.
  eapply Par_lc1; eauto.
Qed.

(* kept for backward compatibility *)
Lemma multipar_lc2: forall G D a1 a2, lc_tm a1 -> multipar G D a1 a2 -> lc_tm a2.
Proof.
  induction 2; eauto.
  apply IHmultipar.
  eapply Par_lc2; apply H0.
Qed.

Lemma multipar_lc2' : forall G D a1 a2, multipar G D a1 a2 -> lc_tm a2.
Proof.
  move => G D a1 a2 H.
  move : (multipar_lc1 H) => h1.
  move : (multipar_lc2 h1 H).
  done.
Qed.

Lemma multipar_lc2_prop: forall G D phi1 phi2, lc_constraint phi1 -> multipar_prop G D phi1 phi2 -> lc_constraint phi2.
  induction 2; eauto.
  apply IHmultipar_prop.
  eapply Par_lc2; apply H0.
Qed.

Lemma multipar_confluence : forall S D a a1, Good S D -> erased_tm a -> multipar S D a a1
-> forall a2, multipar S D a a2 -> exists b, multipar S D a1 b /\ multipar S D a2 b.
Proof.
  intros S D a a1 Es Ea MP. induction MP.
intros.
 - exists a2. split; eauto using multipar_lc2.
 - intros.
   destruct (multipar_confluence_helper Es Ea H0 H) as [d [L R]].
   inversion Es.
   assert (Eb : erased_tm b). eapply Par_erased_tm; eauto.
   destruct (IHMP Es Eb d) as [e [LL RR]]; auto.
   exists e. split; eauto.
Qed.

Lemma multipar_prop_confluence : forall S D phi phi1, Good S D -> erased_constraint phi -> multipar_prop S D phi phi1
-> forall phi2, multipar_prop S D phi phi2 -> exists b, multipar_prop S D phi1 b /\ multipar_prop S D phi2 b.
Proof.
  intros S D phi phi1 Es Ea MP. induction MP.
  intros.
 - exists phi2. split; eauto using multipar_lc2_prop.
 - intros.
   destruct (multipar_prop_confluence_helper Es Ea H0 H) as [d [L R]].
   inversion Es.
   assert (Eb : erased_constraint phi2). eapply Par_erased_constraint; eauto.
   destruct (IHMP Es Eb d) as [e [LL RR]]; auto.
   exists e. split; eauto.
Qed.

Lemma multipar_append : forall S D a b c, multipar S D a b -> multipar S D b c -> multipar S D a c.
Proof.
  intros.
  induction H. auto.
  eauto.
Qed.

Lemma multipar_prop_append : forall S D phi1 phi2 phi3, multipar_prop S D phi1 phi2 -> multipar_prop S D phi2 phi3 -> multipar_prop S D phi1 phi3.
Proof.
  intros.
  induction H. auto.
  eauto.
Qed.



(*
    a   b   c
     \ / \ /
      ab  bc
       \ /
        d
 *)


Lemma join_transitive : forall S D a b, Good S D -> joins S D a b -> forall c, joins S D b c -> joins S D a c.
Proof.
  intros S D a b G H. destruct H as [ab [ES [Ea [Eb [Aab Bab]]]]].
  intros c H. destruct H as [bc [_ [_ [Ec [Bbc Cbc]]]]].
  destruct (multipar_confluence G Eb Bab Bbc) as [d [Babd Bbcd]].
  unfold joins.
  exists d. split. eauto. split. auto.
  split. auto. split; eapply multipar_append; eauto.
Qed.

Lemma joins_constraint_transitive : forall S D phi1 phi2, Good S D -> joins_constraint S D phi1 phi2 -> forall phi3, joins_constraint S D phi2 phi3 -> joins_constraint S D phi1 phi3.
Proof.
  intros S D a b G H. destruct H as [ab [ES [Ea [Eb [Aab Bab]]]]].
  intros c H. destruct H as [bc [_ [_ [Ec [Bbc Cbc]]]]].
  destruct (multipar_prop_confluence G Eb Bab Bbc) as [d [Babd Bbcd]].
  unfold joins_constraint.
  exists d. split. eauto. split. auto.
  split. auto.
  split; eapply multipar_prop_append; eauto.
Qed.

Lemma join_symmetry: forall S D a b, joins S D a b -> joins S D b a.
Proof.
  intros S D a b H.
  destruct H as [ac h0].
  split_hyp.
  exists ac; eauto.
Qed.


Definition extends (G G2 : context) := exists G1, G = G1 ++ G2.



Hint Resolve multipar_context_independent : DB.

Lemma join_context_independent: forall G1 G2 D A B, erased_context G2 ->
                                             joins G1 D A B -> joins G2 D A B.
Proof.
  intros G1 G2 D A B E H.
  destruct H.
  split_hyp.
  unfold joins.
  exists x.
  repeat split; eauto with DB.
Qed.


Lemma interp_constraint_irrel : forall G D G' D' phi, interp_constraint G D phi <-> interp_constraint G' D' phi.
Proof.
  move => G D G' D'; elim; intros.
  - simpl.
    split;
     destruct 1 as [C [Par1 Par2]];
      exists C; split; eauto using context_multipar_irrelevance.
  - simpl.
    split; move : H0 H => h0 h1; tauto.
Qed.
  

Lemma Good_NoAssn: forall c G D phi, erased_sort (Co phi) -> Good G D -> c `notin` D -> Good ((c, Co phi) :: G) D.
Proof.
  intros c G D phi E H Fr.
  unfold Good in *.
  destruct H as (Es & M).
  split.
  + unfold erased_context in *.
    apply Forall_forall.
    intros x0 IN. destruct x0 as (y, s).
    inversion IN.
    - inversion H; subst. auto.
    - eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros c1 c2. intros.
    assert (c <> c1). fsetdec.
    apply binds_cons_1 in H.
    destruct H as [[EQ _] | BI1]. fsetdec.
    rewrite -interp_constraint_irrel. eauto.
Qed.

Hint Resolve Good_NoAssn.

Hint Resolve multipar_context_independent.

Lemma Good_add_tm: forall G D x A,
    erased_tm A -> Good G D -> Good ((x, Tm A)::G ) D.
Proof.
  intros G D x A E H.
  unfold Good in *.
  split.
  + unfold erased_context in *.
    apply Forall_forall.
    intros x0 IN. destruct x0 as (y, s).
    inversion IN.
    - inversion H0. subst. apply erased_Tm. auto.
    - split_hyp.
      eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros.
    move : H => [eG H].
    rewrite -interp_constraint_irrel.
    move : (H c1) => h0.
    inversion H0; subst; auto.
    invert_equality.
Qed.

Lemma Good_add_tm_2: forall G D x A, x `notin` dom G -> erased_tm A -> Good G D -> Good ((x, Tm A)::G ) (add x D).
Proof.
  intros G D x A FR E H.
  unfold Good in *.
  split.
  + unfold erased_context in *.
    apply Forall_forall.
    intros x0 IN. destruct x0 as (y, s).
    inversion IN.
    - inversion H0. subst. apply erased_Tm. auto.
    - split_hyp.
      eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros c1 phi BI1 I1.
    destruct H as (Es & M).
    apply binds_cons_1 in BI1.
    destruct BI1 as [[_ EQ] | BI1]. inversion EQ.
    move: (binds_In _ c1 _ _ BI1) => b0.
    rewrite -interp_constraint_irrel.
    apply (M c1); auto.
    fsetdec.
Qed.

Lemma multipar_app_left_Rel:
  forall a a' c' S D, lc_tm a -> multipar S D a' c' -> multipar S D (a_App a Rel a') (a_App a Rel c').
Proof.
  induction 2; eauto; try done.
Qed.

Lemma multipar_capp_left: forall a a' S D, multipar S D a a' -> multipar S D (a_CApp a g_Triv) (a_CApp a' g_Triv).
Proof.
  induction 1; eauto; try done.
  Unshelve. auto.
Qed.

Lemma multipar_prop_impl_left:
  forall phi1 phi2 phi3 S D, lc_constraint phi1 -> multipar_prop S D phi2 phi3 ->
                        multipar_prop S D (Impl phi1 phi2) (Impl phi1 phi3).
Proof.
  induction 2; eauto; try done.
Qed.

Lemma multipar_prop_impl_right:
  forall phi1 phi2 phi3 S D, lc_constraint phi1 -> multipar_prop S D phi2 phi3 ->
                        multipar_prop S D (Impl phi2 phi1) (Impl phi3 phi1).
Proof.
  induction 2; eauto; try done.
Qed.

Lemma join_capp: forall a a' S D, joins S D a a' -> joins S D (a_CApp a g_Triv) (a_CApp a' g_Triv).
Proof.
  unfold joins.
  intros a a' S D H.
  destruct H as [ac h0].
  split_hyp.
  exists (a_CApp ac g_Triv).
  repeat split; eauto.
  apply multipar_capp_left; auto.
  apply multipar_capp_left; auto.
Qed.

Lemma multipar_app_lr_Rel: forall a a' c c' S D, lc_tm a -> lc_tm a' -> multipar S D a c -> multipar S D a' c' -> multipar S D (a_App a Rel a') (a_App c Rel c').
Proof.
  induction 3; eauto; try done.
  - apply multipar_app_left_Rel; auto.
  - intros H3.
    apply (@mp_step G D _ _ (a_App b Rel a')); eauto.
  (have: lc_tm b by eapply Par_lc2; eauto); eauto.
  Unshelve. auto. auto.
Qed.

Lemma multipar_app_lr_Irrel: forall a c S D, lc_tm a -> multipar S D a c -> multipar S D (a_App a Irrel a_Bullet) (a_App c Irrel a_Bullet).
Proof.
  induction 2; eauto; try done.
  apply (@mp_step G D _ _ (a_App b Irrel a_Bullet)); eauto.
  (have: lc_tm b by eapply Par_lc2; eauto); eauto.
Qed.

Lemma join_app_Rel: forall a a' b b' S D, joins S D a b -> joins S D a' b' -> joins S D (a_App a Rel a') (a_App b Rel b').
Proof.
  unfold joins.
  intros a a' b b' S D H H0.
  destruct H as [ac h0].
  destruct H0 as [ac' h1].
  split_hyp.
  exists (a_App ac Rel ac').
  repeat split; eauto.
  apply multipar_app_lr_Rel; auto; try solve [eapply erased_lc; eauto].
  apply multipar_app_lr_Rel; auto; try solve [eapply erased_lc; eauto].
Qed.

Lemma join_app_Irrel: forall a b S D, joins S D a b -> joins S D (a_App a Irrel a_Bullet) (a_App b Irrel a_Bullet).
Proof.
  unfold joins.
  intros a b S D H.
  destruct H as [ac h0].
  split_hyp.
  exists (a_App ac Irrel a_Bullet).
  repeat split; eauto.
  apply multipar_app_lr_Irrel; auto; try solve [eapply erased_lc; eauto].
  apply multipar_app_lr_Irrel; auto; try solve [eapply erased_lc; eauto].
Qed.

(*
Lemma Par_iapp : forall G D a c y L,
    y `notin` fv_tm_tm_tm a \u L ->
    (forall x, x `notin` L -> RhoCheck Irrel x (open_tm_wrt_tm a (a_Var_f x))) ->
    Par G D (open_tm_wrt_tm a a_Bullet) c ->
    Par G D (a_UAbs Irrel a) (a_UAbs Irrel (close_tm_wrt_tm y c)).
Proof.
  intros.
  eapply (Par_Abs_exists); eauto.
  move: (H0 y ltac:(auto)) => h0.
  inversion h0.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a (a_Var_f y)) a_Bullet y); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
Qed.
 *)

Lemma multipar_UAbs_exists :  ∀ (x : atom) (G : context) (D : available_props)
       (rho : relflag) (a a' : tm),
    x `notin` fv_tm_tm_tm a
       → multipar G D (open_tm_wrt_tm a (a_Var_f x)) a'
         → multipar G D (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')).
Proof.
  intros.
  dependent induction H0.
  autorewrite with lngen. eauto with lngen.
  eapply mp_step.
  eapply Par_Abs_exists with (x:=x); eauto.
  eapply IHmultipar; eauto. autorewrite with lngen. auto.
  autorewrite with lngen. reflexivity.
Qed.

Lemma multipar_iapp : forall G D a c y L,
    y `notin` fv_tm_tm_tm a \u L ->
    (forall x, x `notin` L -> RhoCheck Irrel x (open_tm_wrt_tm a (a_Var_f x))) ->
    multipar G D (open_tm_wrt_tm a a_Bullet) c ->
    multipar G D (a_UAbs Irrel a) (a_UAbs Irrel (close_tm_wrt_tm y c)).
Proof.
  intros.
  eapply multipar_UAbs_exists; auto.
  move: (H0 y ltac:(auto)) => h0.
  inversion h0.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a (a_Var_f y)) a_Bullet y); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
Qed.

Lemma joins_iapp : forall S D a1 a2 L1 L2,
    (forall x, x `notin` L1 -> RhoCheck Irrel x (open_tm_wrt_tm a1 (a_Var_f x))) ->
    (forall x, x `notin` L2 -> RhoCheck Irrel x (open_tm_wrt_tm a2 (a_Var_f x))) ->
    joins S D (open_tm_wrt_tm a1 a_Bullet) (open_tm_wrt_tm a2 a_Bullet) ->
    joins S D (a_UAbs Irrel a1) (a_UAbs Irrel a2).
Proof.
  intros.
  destruct H1 as (C & ES & T1 & T2 & P1 & P2).
  unfold joins.
  pick fresh y.
  exists (a_UAbs Irrel (close_tm_wrt_tm y C)).
  repeat split; eauto.
  eapply (@erased_a_Abs L1).
  intros.
  move: (H x H1) => RC. inversion RC.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a1 (a_Var_f x)) a_Bullet x); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
  move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a1 (a_Var_f x)) => h0. fsetdec. auto.
  eapply (@erased_a_Abs L2).
  intros.
  move: (H0 x H1) => RC. inversion RC.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a2 (a_Var_f x)) a_Bullet x); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
  move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a2 (a_Var_f x)) => h0. fsetdec.
  auto.
  eapply (multipar_iapp _ _ H). eauto.
  eapply (multipar_iapp _ _ H0). eauto.
  Unshelve. eauto. eauto.
Qed.

Lemma multipar_App_destruct_Rel : forall S D a1 a2 c,
    multipar S D (a_App a1 Rel a2) c ->
    (exists a1' a2',
        multipar S D (a_App a1 Rel a2) (a_App (a_UAbs Rel a1') Rel a2') /\
        multipar S D a1 (a_UAbs Rel a1') /\
        multipar S D a2 a2' /\
        multipar S D (open_tm_wrt_tm a1' a2') c) \/
    (exists a1' a2',
        multipar S D (a_App a1 Rel a2) (a_App a1' Rel a2') /\
        multipar S D a1 a1' /\
        multipar S D a2 a2').
Proof.
  intros. dependent induction H.
  + right.
    exists a1, a2. split; auto.
    inversion H; eauto.
  + inversion H; auto; subst.
    assert (lc_tm a1). eapply Par_lc1_tm. eauto.
    assert (lc_tm a2). eapply Par_lc1_tm. eauto.
    subst.
    left.
    exists a'0, b'; repeat split; auto.
    apply multipar_app_lr_Rel; eauto.
    eapply mp_step.
    apply H5.
    apply mp_refl.
    eauto using Par_lc2_tm.
    eapply mp_step.
    apply H7.
    constructor.
    eauto with lc.
    eapply mp_step.
    apply H5.
    apply mp_refl.
    eauto using Par_lc2_tm.
    eapply mp_step.
    apply H7.
    apply mp_refl.
    eauto using Par_lc2_tm.
    destruct (IHmultipar a'0 b') as [[a1' [a2' [P1 [P2 [P3 P4]]]]] |
                                      [a1' [a2' [P1 [P2 P3]]]]] ; auto.
    ++ clear IHmultipar. left.
       exists a1', a2'.
       repeat split; eauto.
    ++ clear IHmultipar. right.
       exists a1', a2'.
       repeat split; eauto.
       Unshelve.
       all: exact G.
Qed.

Lemma multipar_App_destruct_Irrel : forall S D a1 c,
    multipar S D (a_App a1 Irrel a_Bullet) c ->
    (exists a1',
        multipar S D (a_App a1 Irrel a_Bullet) (a_App (a_UAbs Irrel a1') Irrel a_Bullet) /\
        multipar S D a1 (a_UAbs Irrel a1') /\ multipar S D (open_tm_wrt_tm a1' a_Bullet) c) \/
    (exists a1',
        multipar S D (a_App a1 Irrel a_Bullet) (a_App a1' Irrel a_Bullet) /\
        multipar S D a1 a1').
Proof.
  intros. dependent induction H.
  - right.
    exists a1. split; auto.
    inversion H.
    subst. eauto.
  - inversion H; subst; eauto.
    + subst. left.
      exists a'0. split; auto.
      assert (lc_tm a1). eapply Par_lc1. eauto.
      eapply multipar_app_lr_Irrel; eauto.
      all : try split.
      all : solve [eapply mp_step; eauto;  eauto using Par_lc2_tm].
  + assert (lc_tm a1). eapply Par_lc1. eauto.
    subst. edestruct (IHmultipar a'0); auto.
    ++ clear IHmultipar. left. destruct H2 as [a1' K].
       exists a1'. inversion K. inversion H3.  subst.
       repeat split; eauto using Par_lc2_tm with lc.
    ++ clear IHmultipar. right. destruct H2 as [a1' K].
       exists a1'. inversion K. clear K.
       repeat split; eauto.
Unshelve.
all: exact G.
Qed.

Lemma multipar_prop_eq_left:
  forall a b c A S D, lc_tm a -> lc_tm b -> lc_tm A -> multipar S D b c ->
                        multipar_prop S D (Eq a b A) (Eq a c A).
Proof.
  induction 4; eauto; try done.
  apply mpprop_step with (phi2 := Eq a b A).
  constructor; auto.
  apply IHmultipar.
  eauto with lc.
Qed.

Lemma multipar_prop_eq_right:
  forall a b c A S D, lc_tm a -> lc_tm b -> lc_tm A -> multipar S D b c ->
                        multipar_prop S D (Eq b a A) (Eq c a A).
Proof.
  induction 4; eauto; try done.
  apply mpprop_step with (phi2 := Eq b a A).
  constructor; auto.
  apply IHmultipar.
  eauto with lc.
Qed.

Lemma multipar_prop_eq_type:
  forall a b A B S D, lc_tm a -> lc_tm b -> lc_tm A -> multipar S D A B ->
                        multipar_prop S D (Eq a b A) (Eq a b B).
Proof.
  induction 4; eauto; try done.
  apply mpprop_step with (phi2 := Eq a b b0).
  constructor; auto.
  apply IHmultipar.
  eauto with lc.
Qed.

Lemma multipar_prop_eq : forall S D a b A phi2, multipar_prop S D (Eq a b A) phi2 -> exists a' b' A', phi2 = (Eq a' b' A').
Proof.
  intros S D a b A phi2 H.
  dependent induction H; intros; subst; eauto.
  inversion H; eauto.
Qed.

Lemma multipar_prop_eq_rev : forall S D a b A phi2, multipar_prop S D phi2 (Eq a b A) -> exists a' b' A', phi2 = (Eq a' b' A').
Proof.
  intros S D a b A phi2 H.
  dependent induction H; intros; subst; eauto.
  inversion H; subst; eauto.
  contradict IHmultipar_prop.
  move => h1.
  by move : (h1 _ _ _ eq_refl) => [a' [b' [A' EQ]]].
Qed.

Lemma multipar_prop_eq_proj1 : forall S D a b A a' b' A',
    multipar_prop S D (Eq a b A) (Eq a' b' A') -> multipar S D a a'.
Proof.
  intros.
  dependent induction H.
  - inversion H; repeat split; eauto.
  - inversion H; repeat split; subst; eauto.
    Unshelve.
    eauto.
Qed.

Lemma multipar_prop_eq_proj2 : forall S D a b A a' b' A',
    multipar_prop S D (Eq a b A) (Eq a' b' A') -> multipar S D b b'.
Proof.
  intros.
  dependent induction H.
  - inversion H; repeat split; eauto.
  - inversion H; repeat split; subst; eauto.
    Unshelve.
    eauto.
Qed.

Lemma multipar_prop_eq_proj3 : forall S D a b A a' b' A',
    multipar_prop S D (Eq a b A) (Eq a' b' A') -> multipar S D A A'.
Proof.
  intros.
  dependent induction H.
  - inversion H; repeat split; eauto.
  - inversion H; repeat split; subst; eauto.
    Unshelve.
    eauto.
Qed.

Lemma multipar_prop_impl : forall S D phi1 phi2 phi3, multipar_prop S D (Impl phi1 phi2) phi3 -> exists phi4 phi5, phi3 = (Impl phi4 phi5).
Proof.
  intros S D phi1 phi2 phi3 H.
  dependent induction H; intros; subst; eauto.
  inversion H; eauto.
Qed.

Lemma multipar_prop_impl_rev : forall S D phi1 phi2 phi3, multipar_prop S D phi3 (Impl phi1 phi2) -> exists phi4 phi5, phi3 = (Impl phi4 phi5).
Proof.
  intros S D phi1 phi2 phi3 H.
  dependent induction H; intros; subst; eauto.
  inversion H; eauto; subst.
  contradict IHmultipar_prop.
  move => h1.
  by move : (h1 _ _ eq_refl) => [phi5 [phi6 EQ]].
Qed.

Lemma multipar_prop_impl_proj1 : forall S D phi1 phi2 phi3 phi4,
    multipar_prop S D (Impl phi1 phi2) (Impl phi3 phi4) -> multipar_prop S D phi1 phi3.
Proof.
  intros.
  dependent induction H.
  - inversion H; repeat split; eauto.
  - inversion H; repeat split; subst; eauto.
Qed.

Lemma multipar_prop_impl_proj2 : forall S D phi1 phi2 phi3 phi4,
    multipar_prop S D (Impl phi1 phi2) (Impl phi3 phi4) -> multipar_prop S D phi2 phi4.
Proof.
  intros.
  dependent induction H.
  - inversion H; repeat split; eauto.
  - inversion H; repeat split; subst; eauto.
Qed.

Lemma joins_constraint_iff : forall G D, Good G D ->  forall phi1 phi2,
    joins_constraint G D phi1 phi2 -> (interp_constraint G D phi1 <-> interp_constraint G D phi2).
Proof.
  move => G D G_Ok; elim.
  - intros.
    move : H => [phi3 h].
    split_hyp.
    split; intros.
    (* how do I shrink this *)
    + move : (multipar_prop_eq H2) => [a' [b' [A' EQ]]]; subst.
      move : (multipar_prop_eq_rev H3) => [a'' [b'' [A'' EQ]]]; subst.
      move : (multipar_prop_eq_proj1 H2)
               (multipar_prop_eq_proj2 H2)
               (multipar_prop_eq_proj1 H3)
               (multipar_prop_eq_proj2 H3)
           => h0 h1 h3 h4.
      erased_inversion.
      have K0 : joins G D a b.
      simpl in *.
      unfold joins.
      destruct H4.
      split_hyp.
      exists x; split_hyp; auto.

      have K1 : joins G D a a''.
      exists a'; split_hyp; auto.

      have K2 : joins G D b b''.
      exists b'; split_hyp; auto.

      apply join_symmetry in K1.

      have : joins G D a'' b''.
      have : joins G D a'' b.
      eauto using join_transitive.
      eauto using join_transitive.
      simpl.
      unfold joins.
      intros.
      destruct x; split_hyp.
      exists x; tauto.
    + move : (multipar_prop_eq H2) => [a' [b' [A' EQ]]]; subst.
      move : (multipar_prop_eq_rev H3) => [a'' [b'' [A'' EQ]]]; subst.
      move : (multipar_prop_eq_proj1 H2)
               (multipar_prop_eq_proj2 H2)
               (multipar_prop_eq_proj1 H3)
               (multipar_prop_eq_proj2 H3)
           => h0 h1 h3 h4.
      erased_inversion.
      have K0 : joins G D a b.
      simpl in *.
      destruct H4.
      split_hyp.
      apply join_transitive with (b := a''); auto.
      exists a'; repeat split; auto.

      apply join_transitive with (b := b''); auto.
      exists x; repeat split; auto.
      exists b'; repeat split;  auto.

      destruct K0.
      exists x.
      tauto.
  - intros.
    move : H1 => [phi3 h]; split_hyp.
    move : (multipar_prop_impl H4) => [phi4 [phi5 EQ]]; subst.
    move : (multipar_prop_impl_rev H5) => [phi6 [phi7 EQ]]; subst.
    erased_inversion.
    simpl in *.
    move : (multipar_prop_impl_proj1 H4) (multipar_prop_impl_proj2 H4)
           (multipar_prop_impl_proj1 H5) (multipar_prop_impl_proj2 H5)
         => h0 h1 h2 h3.
    simpl.

    have : joins_constraint G D phi1 phi6.
    exists phi4; repeat split; tauto.
    have : joins_constraint G D phi2 phi7.
    exists phi5; repeat split; tauto.
    move => P2 P1.
    move : (H _ P1) (H0 _ P2).
    tauto.
Qed.    
    

  


Lemma consistent_mutual:
  (forall S a A,   Typing S a A -> True) /\
  (forall S phi,   PropWff S phi -> True) /\
  (forall S D p1 p2, Iso S D p1 p2 -> Good S D -> joins_constraint S D p1 p2) /\
  (forall S D phi,   DefEq S D phi -> Good S D -> interp_constraint S D phi) /\
  (forall S,       Ctx S -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; eauto; try done.
  (* new cases for constraints *)
  - move => G D A1 B1 A A2 B2 d1 IH1 d2 IH2 G_Ok.
    unfold joins_constraint.
    simpl in *.
    move : (IH1 ltac:(auto)) (IH2 ltac:(auto)) => [A3 ParA] [B3 ParB].
    move : ParA ParB (IH1 G_Ok) (IH2 G_Ok) => [Par1 Par2] [Par3 Par4] [C1 [Par5 Par6]] [C2 [Par7 Par8]].
    exists (Eq A3 B3 A); repeat split; try apply typing_erased_type_mutual; eauto;
      apply typing_erased_type_mutual in d1;
      apply typing_erased_type_mutual in d2;
      erased_inversion; eauto.
    + apply multipar_prop_append with (phi2 := (Eq A1 B3 A)).
      apply multipar_prop_eq_left; eauto with lc erased.
      apply multipar_prop_eq_right; eauto using multipar_lc2 with lc.
    + apply multipar_prop_append with (phi2 := (Eq A2 B3 A)).
      apply multipar_prop_eq_left; eauto with lc erased.
      apply multipar_prop_eq_right; eauto using multipar_lc2 with lc.
  - move => G D A1 A2 A B d1 IH Eq1Wff _ Eq2Wff _ G_Ok.
    rewrite /joins_constraint.
    rewrite /interp_constraint in IH.
    move : (IH G_Ok) => [C [Par1 Par2]].
    exists (Eq A1 A2 C); repeat split; eauto with erased lc.
    + apply ctx_wff_mutual in d1.
      apply typing_erased_type_mutual in d1.
      assumption.
    + apply typing_erased_type_mutual in Eq1Wff.
      apply typing_erased_type_mutual in Eq2Wff.
      erased_inversion.
      apply multipar_prop_eq_type; auto with lc erased.
    + apply typing_erased_type_mutual in Eq1Wff.
      apply typing_erased_type_mutual in Eq2Wff.
      erased_inversion.
      apply multipar_prop_eq_type; auto with lc erased.
  (* cpifst *)
  - move => G D phi1 phi2 B1 B2 d1 IH1 G_Ok.
    move : (IH1 G_Ok) => h1.
    rewrite /interp_constraint in h1.
    move : h1 => [C [Par1 Par2]].
    Check multipar_CPi.
    move : (multipar_CPi Par1 ltac:(auto)) => h1.
    move : h1 => [phi3 [C2 EQ]]; subst.
    move : (multipar_CPi_phi_proj Par1) (multipar_CPi_phi_proj Par2) => h1 h2.
    exists phi3; repeat split; auto.
    + apply ctx_wff_mutual in d1.
      apply typing_erased_type_mutual.
      assumption.
    + apply typing_erased_type_mutual in d1.
      erased_inversion; auto.
    + apply typing_erased_type_mutual in d1.
      erased_inversion; auto.
  - move => G D phi1 phi3 phi2 phi4 eqPhi1Phi2 IH12 eqPhi3Phi4 IH34 G_Ok.
    move : (IH12 ltac:(auto)) (IH34 ltac:(auto)) => h12 h34.
    move : (IH12 ltac:(auto)) (IH34 ltac:(auto)) => [phi5 [erasedG [erasedPhi1 [erasedPhi2 [Par1 Par2]]]]]
                                                     [phi6 [_ [_ [_ [Par3 Par4]]]]].
    exists (Impl phi5 phi6); repeat split; auto with erased lc.
    + constructor; auto.
      apply typing_erased_type_mutual in eqPhi3Phi4. tauto.
    + constructor; auto.
      apply typing_erased_type_mutual in eqPhi3Phi4. tauto.
    + apply multipar_prop_append with (phi2 := Impl phi1 phi6); auto.
      apply multipar_prop_impl_left; auto with erased lc.
      apply multipar_prop_impl_right; auto with erased lc.
      apply multipar_lc2_prop in Par4; auto.
      apply typing_erased_type_mutual in eqPhi3Phi4.
      destruct eqPhi3Phi4.
      auto with lc.
    + apply multipar_prop_append with (phi2 := Impl phi2 phi6); auto.
      apply multipar_prop_impl_left; auto with erased lc.
      apply multipar_prop_impl_right; auto with erased lc.
      apply multipar_lc2_prop in Par4; auto.
      apply typing_erased_type_mutual in eqPhi3Phi4.
      destruct eqPhi3Phi4.
      auto with lc.
  - (* assn *)
    move => G D phi c CtxG _ Hbinds Hc G_Ok.
    rewrite /Good in G_Ok.
    move : G_Ok => [H0 H1].
    eauto.
  - (* reflexivity *)
    move => G D a A wtA _ G_Ok.
    rewrite /interp_constraint.
    apply typing_erased_mutual in wtA.
    exists a. split; auto with lc.
  - (* symmetry *)
    move => G D a b A d H G_Ok.
    unfold interp_constraint in *.
    move : (H ltac:(auto)) => [c [Par1 Par2]].
    exists c; tauto.
  - (* transitivity *)
    move => G D a c A b  d1 IH1 d2 IH2 G_Ok.
    move : (IH1 G_Ok) (IH2 G_Ok) => h1 h2.
    move : (IH1 G_Ok) (IH2 G_Ok) => [C0 [H0 H1]] [C1 [H2 H3]].
    have : erased_context G. apply ctx_wff_mutual in d1. eapply typing_erased_type_mutual; assumption.
    have : erased_tm a.
    apply typing_erased_type_mutual in d1; erased_inversion; auto.
    have : erased_tm b.
    apply typing_erased_type_mutual in d1; erased_inversion; auto.
    have : erased_tm c.
    apply typing_erased_type_mutual in d2; erased_inversion; auto.
    move => ec eb ea eG.
    have : joins G D a b.
    rewrite /joins.
    exists C0; repeat split; auto.
    have : joins G D b c.
    rewrite /joins.
    exists C1; repeat split; auto.
    move => h3 h4.
    move : (join_transitive G_Ok h4 h3) => h5.
    rewrite /joins in h5.
    destruct h5.
    split_hyp.
    rewrite /interp_constraint.
    exists x.
    auto.
  - (* confluence *)
    intros G. intros.
    inversion H.
    unfold joins in *. subst.
    have : erased_tm a1.
    apply typing_erased_mutual in t; assumption.
    have : erased_tm a2.
    apply typing_erased_mutual in t0; assumption.
    have p: Par G D a1 a2.
    { inversion b.
      eapply Par_Beta; eauto 2. eauto using Value_lc.
      eapply Par_CBeta; eauto 2.
      eapply Par_Axiom; eauto 2.
      }
    rewrite /interp_constraint.
    exists a2; split; eauto with lc.
  - (* pi-cong *)
    intros L G D rho A1 B1 A2 B2 d H d0 H0 _ _ t H1 t0 H2 H3.
    have : erased_tm A2.
    apply typing_erased_type_mutual in d; erased_inversion; auto.
    move => eA2.
    inversion H3.
    have e0: erased_tm (a_Pi rho A1 B1). eapply Typing_erased_tm; eauto.
    inversion e0. subst.
    pose Ih1 := H H3.
    apply Typing_erased_tm in t0.
    erased_inversion.
    pick fresh x for (L \u (fv_tm_tm_tm B1) \u (fv_tm_tm_tm B2) \u dom G \u L0 \u L1 \u L2).
    assert (G' : Good ([(x, Tm A1)] ++ G) D).
    { apply Good_add_tm; auto. }
    have: x `notin` L; auto => fr.
    pose Ih2 := H0 x fr G'.
    destruct H as [A'' h1]; auto; subst.
    destruct Ih2 as [B'' h2].
    split_hyp.
    exists (a_Pi rho A'' (close_tm_wrt_tm x B'')); eauto.
    repeat split; eauto 1.
    + apply multipar_Pi_exists; auto.
      apply (lc_a_Pi_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
    + apply multipar_Pi_exists; auto.
      apply (lc_a_Pi_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
  - (* abs-cong *)
    intros L G D rho b1 b2 A1 B IHDefEq H1 t _ RC1 RC2 GOOD.
    inversion GOOD.
    have e0: erased_tm A1. eapply Typing_erased_tm; eauto.
    pick fresh x for (L \u (fv_tm_tm_tm b1) \u (fv_tm_tm_tm b2)).
    assert (G' : Good ([(x, Tm A1)] ++ G) D).
    apply Good_add_tm; auto.
    have: x `notin` L; auto => fr.
    pose Ih2 := H1 x fr G'.
    have: erased_tm (open_tm_wrt_tm b1 (a_Var_f x)) /\ erased_tm (open_tm_wrt_tm b2 (a_Var_f x)).
    move : (IHDefEq x fr) => h3.
    apply typing_erased_type_mutual in h3.
    erased_inversion; tauto.
    move => [eb1 eb2].
    destruct Ih2 as [B'' h2].
    split_hyp.
    exists (a_UAbs rho (close_tm_wrt_tm x B'')); eauto.
    repeat split; eauto 1.
    + apply multipar_Abs_exists; auto.
      apply (lc_a_UAbs_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
    + apply multipar_Abs_exists; auto.
      apply (lc_a_UAbs_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
  (* interp_constraint does not include the erased preconditions *)
  - move => G D a1 a2 b1 b2 d H d0 H0 p H1 H2.
    have : erased_context G.
    apply ctx_wff_mutual in d0.
    apply typing_erased_type_mutual; assumption.
    have : erased_tm a1 /\ erased_tm b1.
    apply typing_erased_type_mutual in d0; erased_inversion; auto.
    have : erased_tm a2 /\ erased_tm b2.
    apply typing_erased_type_mutual in p; erased_inversion; auto.
    move => [ea2 eb2] [ea1 eb1] eG.
    have : joins G D a1 b1.
    unfold joins.
    simpl in H0.
    move : (H0 H2) => [C [Par1 Par2]].
    exists C; repeat split; eauto.
    have : joins G D a2 b2.
    unfold joins.
    simpl in H1.
    move : (H1 H2) => [C [Par1 Par2]].
    exists C; repeat split; eauto.
    move => Par2 Par1.
    have : joins G D (a_App a1 Rel a2) (a_App b1 Rel b2).
    apply join_app_Rel; auto.
    unfold joins, interp_constraint.
    move => [c [_ [e0 [e1 [Par3 Par4]]]]].
    eauto.
  - move => G D a1 b1 B a A d H t _ H1.
    move : (H H1) => h0.
    
    have : erased_context G.
    apply ctx_wff_mutual in d.
    apply typing_erased_type_mutual.
    assumption.

    have : erased_tm a1 /\ erased_tm b1.
    apply typing_erased_type_mutual in d.
    erased_inversion; tauto.

    move => [ea1 eb1] eG.

    have : joins G D a1 b1.
    rewrite /interp_constraint in h0.
    move : h0 => [c1 [Par1 Par2]].
    rewrite /joins.
    exists c1; eauto.

    move => Par1.
    have : joins G D (a_App a1 Irrel a_Bullet) (a_App b1 Irrel a_Bullet).
    apply join_app_Irrel.
    assumption.

    rewrite /joins.
    rewrite /interp_constraint.
    move => [c HHH].
    exists c. tauto.

  - move => G D A1 A2 rho B1 B2 H IHDefEq GOOD.
    inversion GOOD.

    have : erased_tm A1 /\ erased_tm A2.
    apply typing_erased_type_mutual in H.
    erased_inversion; tauto.
    move => [eA1 eA2].
    
    destruct (IHDefEq GOOD); auto.
    split_hyp.
    move : (multipar_Pi H3 eq_refl) => [A' [B' h0]].
    subst.
    apply multipar_Pi_A_proj in H2.
    apply multipar_Pi_A_proj in H3.
    exists A'; eauto.
    apply erased_lc; eauto.
    apply erased_lc; eauto.
  - intros G D B1 a1 B2 a2 rho A1 A2 H IHDefEq1 H0 IHDefEq2 GOOD.
    inversion GOOD.
    destruct IHDefEq1; auto.
    destruct IHDefEq2 as [ac h0]; auto.
    split_hyp.
    move : (multipar_Pi H3 eq_refl) => [A' [B' h0]].
    subst.
    apply (multipar_Pi_B_proj) in H6.
    apply (multipar_Pi_B_proj) in H3.
    destruct H6 as [L1 h9].
    destruct H3 as [L2 h10].

    apply typing_erased_type_mutual in H.
    apply typing_erased_type_mutual in H0.
    erased_inversion.

    pick_fresh x.
    exists (open_tm_wrt_tm B' ac).


Ltac subst_tm_erased_open x :=
  let K := fresh in
  let h0 := fresh in
  match goal with
  | [H16 : ∀ x : atom, x `notin` ?L0 →
                       erased_tm  (open_tm_wrt_tm ?B (a_Var_f x)),
     H2 : erased_tm ?a
     |- erased_tm (open_tm_wrt_tm ?B ?a) ] =>
    have: x `notin` L0; auto => h0;
    pose K := subst_tm_erased x H2 (H16 x h0);
    clearbody K;
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; auto; try solve [apply erased_lc; auto];
    simpl in K;
    destruct eq_dec; try congruence;
    rewrite tm_subst_tm_tm_fresh_eq in K; auto
  end.

Ltac multipar_subst_open x :=
  let K := fresh in
  let h1 := fresh in
  let h0 := fresh in
  let h2 := fresh in
  let lc1 := fresh in
  match goal with
    [
      H2 : erased_tm ?a1,
      H4 : multipar ?G ?D ?a1 ?ac,
      H18: ∀ x : atom, x `notin` ?L0 → erased_tm (open_tm_wrt_tm ?B1 (a_Var_f x)),
      H9 : ∀ x : atom,
       x `notin` ?L1
       → multipar ?G ?D (open_tm_wrt_tm ?B1 (a_Var_f x)) (open_tm_wrt_tm ?B' (a_Var_f x))
    |-
    multipar ?G ?D (open_tm_wrt_tm ?B1 ?a1) (open_tm_wrt_tm ?B' ?ac) ] =>
      have: x `notin` L0; auto => h0;
      have: x `notin` L1; auto => h1;

      pose K := multipar_subst3 x H2 H4 (H18 x h0) (H9 x h1);
      clearbody K;
      (have: lc_tm a1 by eapply erased_lc_tm; eauto) => lc1;
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K;
      eauto;try solve [eapply multipar_lc2; eauto | eapply multipar_lc2; eauto];
      simpl in K;
      destruct eq_dec; try congruence;
      repeat rewrite tm_subst_tm_tm_fresh_eq in K; auto
   end.
  simpl in *.


  repeat split; eauto.
    + multipar_subst_open x.
    + multipar_subst_open x.
  - (* cpi-cong *)
    intros L G D phi1 A phi2 B H hi0 H1 IHDefEq H2 _ wtA _  wtB _ GOOD .
    move : (hi0 GOOD) => h0.
    simpl.

    apply typing_erased_mutual in wtA.
    apply typing_erased_mutual in wtB.
    erased_inversion.
    pick_fresh c.
    have : erased_tm (open_tm_wrt_co B (g_Var_f c)) /\ erased_tm (open_tm_wrt_co A (g_Var_f c)); auto.
    move => [eB eA].

    destruct (IHDefEq c) as [Ac h1]; eauto.
    + apply Good_NoAssn; auto.
      apply typing_erased_type_mutual in H2.
      constructor.
      auto.
    + split_hyp.
      unfold joins in *.
      move : h0 => [phi3 hphi3].
      split_hyp.
      exists (a_CPi phi3 (close_tm_wrt_co c Ac)); eauto.
      repeat split; eauto 1.
      * Ltac multipar_CPi c :=
        apply multipar_CPi_exists; auto;
        [ apply (lc_a_CPi_exists c); try constructor; apply erased_lc; auto |
          eapply multipar_context_independent; eauto].
        multipar_CPi c.
      * multipar_CPi c.
  - intros L G D a b phi1 B hi0 IHDefEq H1 _ GOOD.
    simpl.

    pick_fresh c.
    
    have [ephi1 ephi'] : erased_sort (Co phi1) /\ erased_constraint phi1.
    apply typing_erased_type_mutual in H1.
    split; auto.
    constructor.
    auto.

    inversion GOOD.

    move : (hi0 c ltac:(fsetdec)) => h0.
    apply typing_erased_type_mutual in h0.
    erased_inversion.
    
    destruct (IHDefEq c) as [Ac h1]; auto.
    + apply Good_NoAssn; auto.
    + split_hyp.
      unfold joins in *.
      exists (a_UCAbs (close_tm_wrt_co c Ac)); eauto.
      split_hyp.
      repeat split; eauto 1.
      * apply multipar_CAbs_exists; auto.
        apply (lc_a_UCAbs_exists c); try constructor; apply erased_lc; auto.
        eapply multipar_context_independent; eauto.
      * apply multipar_CAbs_exists; auto.
        apply (lc_a_UCAbs_exists c); try constructor; apply erased_lc; auto.
        eapply multipar_context_independent; eauto.
  - move => G D a1 b1 B phi d H p H0 H1.
    simpl in *.

    have h : erased_context G.
    apply ctx_wff_mutual in d.
    by apply typing_erased_type_mutual.
    
    apply typing_erased_type_mutual in d.
    erased_inversion.

    have h0 : joins G D a1 b1.
    move : (H H1) => [C [Par1 Par2]].
    exists C; auto; repeat split; auto.

    apply join_capp in h0.

    move : h0 => [C h1].
    exists C. tauto.
  - move => G D B1 B2 phi1 phi2 H0 IHDefEq hi1 IHDefEq2 hi0 IHDefEq3 GOOD.
    destruct IHDefEq as [Ac h0]; eauto.
    split_hyp.
    move : (multipar_CPi H eq_refl) => [phi3 [C2 EQ]]; subst.
    apply multipar_CPi_B_proj in H.
    apply multipar_CPi_B_proj in H1.
    move : H1 H => [L1 H3] [L2 H4].
    inversion GOOD.
    pick_fresh c.
    exists (open_tm_wrt_co C2 g_Triv).
    simpl in *.
    repeat split; eauto 1.
    + Ltac multipar_open_tm_wrt_co c B1 :=
        let K:= fresh in
        let h1:= fresh in
        match goal with
        [ H3 : ∀ c : atom, c `notin` ?L1 →
                           multipar ?G ?D (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co ?Bc' (g_Var_f c))
          |- _ ] =>
        have: c `notin` L1; auto => h1;
        pose K := multipar_subst4 c lc_g_Triv (H3 c h1);
        clearbody K;
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; eauto;
        simpl in K;
        destruct eq_dec; try congruence;
          repeat rewrite co_subst_co_tm_fresh_eq in K; auto
        end.
      multipar_open_tm_wrt_co c B1.
    + multipar_open_tm_wrt_co c B2.
  - move => G D phi2 phi1 d H i H0 H1.
    move: (H0 H1) => h1.
    move: (H H1) => h0.
    split_hyp.
    apply joins_constraint_iff in h1; auto.
    tauto.
  - intros G D A A' a b a' b' i H H0.
    destruct (H H0); split_hyp; auto.
    Unshelve. all: auto.
    move : (multipar_prop_eq H4) => [a'0 [b'0 [A'0 EQ]]]; subst.
    apply multipar_prop_eq_proj3 in H5.
    apply multipar_prop_eq_proj3 in H4.
    exists A'0; repeat split; auto.
  - intros.
    inversion H0.
    unfold joins.
    have: Par G D b b. eauto using Typing_lc1. move => Pb.
    exists b. repeat split; eauto 2 using Typing_erased_tm.
    eapply mp_step with (b := b); eauto with lc.
    apply typing_erased_mutual in t; erased_inversion; eauto with lc.
  - intros.
    inversion H0.
    unfold joins.
    have: Par G D b b. eauto using Typing_lc1. move => Pb.
    exists b. repeat split; eauto 2 using Typing_erased_tm.
    eapply mp_step with (b := b); eauto;
      apply typing_erased_mutual in t; erased_inversion; eauto with lc.
    apply typing_erased_mutual in t; erased_inversion; eauto with lc.
  - intros.
    inversion H0.
    unfold joins.
    have: Par G D b b. eauto using Typing_lc1. move => Pb.
    exists b. repeat split; eauto 2 using Typing_erased_tm.
    eapply mp_step with (b := b); eauto.
    all : apply typing_erased_mutual in t; erased_inversion; eauto with lc.
  - move => G D phi2 phi1 d1 IH1 d2 IH2 G_Ok.
    simpl in *.
    tauto.
  - intros.
    simpl in *.
    intros.
    rewrite interp_constraint_irrel.
    apply H.
    unfold Good in *.
    split_hyp.
    split.
    + apply ctx_wff_mutual in d.
      by apply typing_erased_type_mutual in d.
    + intros.
      have : c `notin` dom G.
      apply ctx_wff_mutual in d.
      apply Ctx_uniq in d.
      inversion d; subst.
      auto.
      apply binds_cons_1 in H3.
      destruct H3; split_hyp; subst.
      * inversion H5; subst.
        rewrite interp_constraint_irrel.
        intros; apply H1.
      * intros.
        rewrite interp_constraint_irrel.
        apply (H2 c1); auto.
        destruct (c1 == c); subst; auto.
        apply binds_In in H3.
        fsetdec.
        fsetdec.
Qed.


Lemma consistent_defeq_phi: forall S D phi,   DefEq S D phi -> Good S D -> interp_constraint S D phi.
Proof.
  apply consistent_mutual.
Qed.

Lemma consistent_defeq: forall S D A B T,   DefEq S D (Eq A B T) -> Good S D -> joins S D A B.
Proof.
  intros.
  move : (consistent_defeq_phi H) => h1.
  destruct h1; split_hyp; auto.
  exists x.
  have : erased_context S.
  apply ctx_wff_mutual in H.
  apply typing_erased_type_mutual.
  auto.
  have : erased_tm A /\ erased_tm B.
  apply typing_erased_type_mutual in H.
  erased_inversion; auto.
  tauto.
Qed.

(* ------------------------------------------------------- *)

Lemma no_aAbs : forall G rho A' a A, Typing G (a_Abs rho A' a) A -> False.
Proof.
  intros. dependent induction H. by apply: IHTyping1.
Qed.

Lemma no_aCAbs : forall G A' a A, Typing G (a_CAbs A' a) A -> False.
Proof.
  intros. dependent induction H; by apply: IHTyping1.
Qed.



Lemma Good_nil : forall D, Good nil D.
Proof.
  intro D.
  unfold Good. split.  done.
  intros. inversion H.
Qed.

Lemma consistent_Star : forall A0,
    consistent a_Star A0 -> value_type A0 -> A0 = a_Star.
Proof.
  intros A0 C V.
  destruct A0; try destruct rho;
    simpl in *; inversion C; inversion V.
  all: subst; auto.
  all: try solve [inversion H].
  all: try solve [inversion H2].
  all: done.
Qed.


Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm a) /\ Good G D.

Lemma irrelevant_Good : forall G D a, irrelevant G D a -> Good G D.
intros. inversion H.
auto.
Qed.
(*
Ltac impossible_defeq A B :=
  match goal with
  | h0 : DefEq G A B a_Star =>
    apply consistent_defeq in h0; eauto;
    apply join_consistent in h0;
 *)
(*
Ltac impossible_Path :=
  match goal with
     [H : Path ?T (a_Pi _ _ _) |- _] => inversion H
   | [H : Path ?T a_Star |- _] => inversion H
   | [H : Path ?T (a_CPi _ _) |- _] => inversion H
  end.
*)

(* When we have a defeq in the context between two value types, show that it
   can't happen. *)
Ltac impossible_defeq :=
  let h0 := fresh in
  let VT := fresh in
  let VT2 := fresh in
  match goal with
  | [ H : DefEq ?G (dom ?G) (Eq ?B ?A ?C) |- _ ] =>
    pose h0:= H; clearbody h0;
    apply consistent_defeq in h0; eauto;
    [apply join_consistent in h0;
     move : (DefEq_lc H) => h1; lc_inversion 1 ; subst;
     have VT: value_type A; eauto;
     have VT2 : value_type B; eauto;
     inversion h0; subst; (* try impossible_Path; *)
     eauto; try done | eapply irrelevant_Good; eauto]
  end.

Lemma canonical_forms_Star : forall G a, irrelevant G (dom G) a ->
    Typing G a a_Star -> Value a -> value_type a.
Proof.
  intros G a IR H V. induction V; auto.
  - subst. assert False. eapply no_aAbs. eauto 2. done.
  - subst. apply invert_a_UAbs in H; eauto.
    destruct H as [A1 [B2 [H _]]].
    impossible_defeq.
  - subst. apply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & DE & TA1 & TA2).
    impossible_defeq.
  - subst. assert False. eapply  no_aAbs. eauto 2. done.
  - subst.  assert False. eapply no_aCAbs. eauto 2. done.
  - subst. apply invert_a_UCAbs in H; eauto.
    destruct H as [a0 [b [T [B1 [_ [H _]]]]]].
    impossible_defeq.
Qed.



Lemma DefEq_Star: forall A G D, Good G D -> value_type A -> DefEq G D (Eq A a_Star a_Star) -> A = a_Star.
Proof.
  intros A G D Good H0 H.
  apply consistent_defeq in H; eauto.
  apply join_consistent in H.
  inversion H;  eauto; subst; try done.
Qed.

Lemma canonical_forms_Pi : forall G rho a A B, irrelevant G (dom G) a ->
    Typing G a (a_Pi rho A B) -> Value a ->
    (exists a1, a = a_UAbs rho a1). (* \/ (exists T, Path T a). *)
Proof.
  intros G rho a A B IR H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & H & _); eauto.
    impossible_defeq.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & B1 & H & _); eauto.
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - assert False. eapply no_aCAbs. eauto 2. done.
  - eapply invert_a_UCAbs in H; eauto.
    destruct H as [a [b [T [B1 [_ [H _]]]]]]; eauto.
    impossible_defeq.
Qed.

Lemma canonical_forms_CPi : forall G a phi B, irrelevant G (dom G) a ->
    Typing G a (a_CPi phi B) -> Value a ->
    (exists a1, a = a_UCAbs a1) (* \/ (exists T, Path T a). *).
Proof.
  intros G a phi B IR H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [H _]]]; eauto.
    impossible_defeq.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [H _]]]; eauto.
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - assert False. eapply no_aCAbs. eauto 2. done.
Qed.




(* helper tactic for progress lemma below. Dispatches goals of the form
   "irrelevant G a " by inversion on IR, a similar assumption in the context *)
Ltac show_irrelevant IR :=
        let x := fresh in
        let A0 := fresh in
        let B0 := fresh in
        let h0 := fresh in
        let h1 := fresh in
        unfold irrelevant in *;
        move: IR => [h0 h1]; split; auto;
        intros x A0 B0;  apply h0 in B0; simpl in B0; fsetdec.

Lemma notin_sub : forall x a b, x `notin` a -> b [<=] a -> x `notin` b.
  intros. fsetdec.
Qed.



(*
   The progress lemma is stated in terms of the reduction_in_one relation.
*)

Lemma progress : forall G a A, Typing G a A ->
                          irrelevant G (dom G) a ->
                          Value a \/ exists a', reduction_in_one a a'.
  induction 1; intros IR; subst; eauto; try done.
  - unfold irrelevant in *.
    move: IR => [H1 _].
    apply H1 in H0. simpl in H0. fsetdec.
  - left; eauto.
    constructor.
    apply (Typing_lc H1); eauto.
    pick_fresh x.
    have: x `notin` L; auto => h0.
    apply (lc_a_Pi_exists x).
    apply (Typing_lc H1); eauto.
    apply (Typing_lc (H x h0)); eauto.
  - destruct rho.
    + left.
    constructor; eauto.
    pick_fresh x.
    have: x `notin` L; auto => h0.
    apply (lc_a_UAbs_exists x).
    apply (Typing_lc (H x h0)); eauto.
    + pick fresh x.
      assert (x `notin` L). auto.
      move: (H2 x H3) => h0.
      inversion h0. subst.
      destruct (H0 x H3) as [V | [a' R]].
      { move: (H x H3) => h1.
      unfold irrelevant in *.
      destruct IR as [h2 h3].
      have ctx: (Ctx ([(x, Tm A)] ++ G)) by eauto.
      move: (Ctx_uniq ctx) => u. inversion u. subst.
      split. intros x0 A0 b0.
      apply binds_cons_uniq_1 in b0. destruct b0.
      ++ split_hyp. subst. auto.
      ++ split_hyp.
         move: (h2 _ _ H5) => fr. simpl in fr.
         eapply notin_sub; [idtac|eapply fv_tm_tm_tm_open_tm_wrt_tm_upper].
         simpl.
         fsetdec.
      ++ eauto.
      ++ simpl. eapply Good_add_tm_2; eauto using Typing_erased_tm. }
      -- left.
         eapply Value_UAbsIrrel_exists with (x := x); eauto.
      -- right. exists (a_UAbs Irrel (close_tm_wrt_tm x a')).
         eapply E_AbsTerm_exists with (x := x).
         { eapply notin_union; auto.
           simpl. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto. }
         rewrite open_tm_wrt_tm_close_tm_wrt_tm. auto.
  - destruct IHTyping1 as [V | [b' h0]].
    + show_irrelevant IR.
    + apply canonical_forms_Pi in H; auto.
      destruct H as [a1 e1]; subst.
      ++ right.
         exists (open_tm_wrt_tm a1 a); eauto.
         apply E_AppAbs; eauto.
         eauto using Value_lc.
         apply (Typing_lc H0); eauto.
      ++ show_irrelevant IR.
    + right.
      exists (a_App b' Rel a); eauto.
      apply E_AppLeft; eauto.
      apply (Typing_lc H0); eauto.
  - case IHTyping1; auto.
    + show_irrelevant IR.
    + move => h1.
      apply canonical_forms_Pi in H; auto.
      destruct H as [a1 e1]; subst.
      ++ right.
      exists (open_tm_wrt_tm a1 a_Bullet); eauto.
      ++ show_irrelevant IR.
    + move => h1.
      destruct h1 as [b' h0].
      right.
      exists (a_App b' Irrel a_Bullet); eauto.
  - left.
    constructor; eauto.
    apply (PropWff_lc H1); eauto.
    pick_fresh c.
    have: c `notin` L; auto => h0.
    apply (lc_a_CPi_exists c); eauto 1.
    apply (PropWff_lc H1); eauto.
    apply (Typing_lc (H c h0)); eauto.
  - left.
    constructor; eauto.
    pick_fresh c.
    have h0: c `notin` L; auto.
    apply (lc_a_UCAbs_exists c); eauto 0.
    apply (Typing_lc (H c h0)); eauto.
  - case IHTyping; auto.
    + show_irrelevant IR.
    + move => h1.
      apply canonical_forms_CPi in H; auto.
      destruct H as [a2 e1]; subst.
      ++
        right. exists (open_tm_wrt_co a2 g_Triv); eauto.
        eapply E_CAppCAbs; eauto.
        eauto using Value_lc.
      ++ show_irrelevant IR.
    + intros H1.
      destruct H1 as [a' h0].
      right.
      exists (a_CApp a' g_Triv); eauto.
      (* what is this? *)
      Unshelve. eauto.
Qed.




End ext_consist.

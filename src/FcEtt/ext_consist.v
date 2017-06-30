
Require Import FcEtt.sigs.

Require Import Omega.

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

Module ext_consist (invert : ext_invert_sig)(fc_wf: fc_wf_sig).
Import invert.
Import fc_wf.

Module red_one := ext_red_one invert.
Export red_one.

Module red := ext_red invert.
Export red.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Definition Good (G : context) (D : available_props):=
  erased_context G /\
  forall c1 A B1 T1 R,
    binds c1 (Co (Eq A B1 T1 R)) G
    -> c1 `in` D
    -> exists C, Par G D A C /\ Par G D B1 C.

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


Lemma a_Pi_head : forall S G b A R rho B,
    Par S G (a_Pi rho A R B) b -> exists A' B' L,
      b = a_Pi rho A' R B' /\ Par S G A A' /\
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
    (exists a', Par G D a' b /\ forall x, x `notin`  fv_tm_tm_tm a ->
          open_tm_wrt_tm a (a_Var_f x) = a_App a' rho (a_Var_f x)).

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
Qed.

(* -------------------------------------------------------------------------------- *)

Ltac try_refl :=
  try match goal with
      | [ P2 : Par _ _ _ ?b |- _ ] =>
        exists b; assert (lc_tm b); try eapply Par_lc2; eauto; try split; eauto; fail
      end.


Ltac invert_equality :=
  match goal with
  | [ H : _ = _ |- _ ] =>
    inversion H
  end.

  Ltac try_refl_left :=
  try match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?b cc /\ Par ?S ?D ?a2 cc ] =>
        exists a2; assert (lc_tm a2); try eapply Par_lc2; eauto; try split; eauto; fail
      end.
  Ltac try_refl_right :=
  try match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?a2 cc /\ Par ?S ?D ?b cc ] =>
        exists a2; assert (lc_tm a2); try eapply Par_lc2; eauto; try split; eauto; fail
      end.

  Ltac invert_erased :=
    match goal with
    | [ H : erased_tm ?a |- _ ] => inversion H; subst; clear H
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
        [ H18 : ∀ x : atom,
              x `notin` ?L0
              → open_tm_wrt_tm ?a (a_Var_f x) = a_App ?b0 ?rho (a_Var_f x)
              |- _ ] =>
        pick fresh x for (L0 \u  fv_tm_tm_tm a \u fv_tm_tm_tm b0);
        move: (H18 x ltac:(auto)) => h1; clear H18;
        rewrite (@tm_subst_tm_tm_intro x a); auto; rewrite h1;
        simpl; destruct (@eq_dec tmvar _ x x); try done;
        rewrite tm_subst_tm_tm_fresh_eq; auto
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
  end.

  Ltac use_size_induction a ac Par1 Par2 :=
  match goal with
  | [   IH : forall y: nat, ?T,
        H2 : Good ?G ?D,
        H3 : erased_tm a,
        H : Par ?G ?D a ?b0,
        H4 : Par ?G ?D a ?b1 |- _ ] =>
      move: (@IH (size_tm a) ltac:(omega) a ltac:(auto) _ _ _ H2 H3 H _ H4) => [ ac [Par1 Par2]]
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
    pose J := subst3 x Par4 KK K;
    clearbody J;
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in J; [auto;
    simpl in J;
    destruct eq_dec; try congruence;
    repeat rewrite tm_subst_tm_tm_fresh_eq in J; auto
    | try apply (Par_lc2 Par4); auto
    | apply (Par_lc1 Par4); auto]
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


Lemma confluence_size : forall n a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
Proof.
  pose confluence_size_def n :=
      forall a, size_tm a <= n ->  forall S D a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
  intro n. fold (confluence_size_def n).  eapply (well_founded_induction_type lt_wf).
  clear n. intros n IH. unfold confluence_size_def in *. clear confluence_size_def.
  intros a SZ S D a1 Gs Ea P1 a2 P2.
  inversion P1; inversion P2; subst.
  all: try solve [invert_equality].
  (* 37 subgoals *)
  (* TODO: there may be a way to check the number of subgoals (and guard against a innvalid number) *)

  all: try_refl_left.
  all: try_refl_right.
  all: try invert_syntactic_equality.
  all: simpl in SZ; destruct n; try solve [ inversion SZ ].
  all: invert_erased; inversion Gs.

  - (* two betas *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    destruct (Par_Abs_inversion Par1) as [[a'' [EQ h0]]| [ax [X1 X2]]]; subst;
    destruct (Par_Abs_inversion Par2) as [[a''' [EQ2 h1]]| [ay [Y1 Y2]]]; subst.
    -- inversion EQ2. subst.
       exists (open_tm_wrt_tm a''' bc).
       split. pick fresh x; eapply open2; eauto using Par_erased_tm.
       pick fresh x; eapply open2; eauto using Par_erased_tm.
    -- exists (open_tm_wrt_tm a'' bc).
       split.
       pick fresh x; eapply open2; eauto using Par_erased_tm.
       eta_expand x.
    -- exists (open_tm_wrt_tm a''' bc).
       split.
       eta_expand x.
       pick fresh x; eapply open2; eauto using Par_erased_tm.
    -- exists (a_App ac rho bc).
       split.
       eta_expand x.
       eta_expand x.
       Unshelve. all: exact D.
  - (* app beta / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    invert_erased_tm (a_UAbs rho a').
    inversion Par1; subst; clear Par1.
    -- exists (open_tm_wrt_tm a' bc); auto.
      split; eauto.
      apply open1 with (L:=L); eauto.
    -- exists (open_tm_wrt_tm a'1 bc); auto.
      split; eauto.
      pick_fresh x.
      par_erased_open x J Par3.
  - (* app cong / app beta *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    invert_erased_tm (a_UAbs rho a'0).
    destruct (Par_Abs_inversion Par2) as [ [a'' [EQ X]] | [b0 [Par5 Y]]].
    * subst.
      exists (open_tm_wrt_tm a'' bc).
      split; eauto.
      pick fresh x; eapply open2; eauto.
      eapply Par_erased_tm; eauto.
    * exists (a_App ac rho bc).
      split.
      eauto.
      eta_expand x.
  - (* app cong / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    exists (a_App ac rho bc). split; auto.
  - (* two cbetas *)
    use_size_induction a0 ac Par1 Par2.
    invert_erased_tm (a_UCAbs a').
    invert_erased_tm (a_UCAbs a'0).
    inversion Par1; inversion Par2; subst; invert_syntactic_equality.
    -- invert_lc.
       exists  (open_tm_wrt_co a' g_Triv); eauto.
       split; eauto 1; apply Par_Refl; apply (Par_lc2) in P2; auto.
    -- invert_lc.
       exists (open_tm_wrt_co a' g_Triv); eauto.
       finish_open_co a'0.
    -- invert_lc.
       exists (open_tm_wrt_co a'1 g_Triv); eauto.
      finish_open_co a'.
    -- exists (open_tm_wrt_co a'1 g_Triv); eauto.
      split; eauto.
      * finish_open_co a'.
      * finish_open_co a'0.
  - (* cbeta / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    inversion P2; subst; clear P2.
    + exists (open_tm_wrt_co a' g_Triv).
      split; eauto.
      apply Par_lc2 in H.
      inversion H; subst.
      pick_fresh c.
      match goal with
        [ h : lc_tm (a_UCAbs ?a')|- _] => inversion h; clear h; subst
      end.
      move: (co_subst_co_tm_lc_tm _ g_Triv c ltac:(eauto) lc_g_Triv) => Kip.
      repeat rewrite co_subst_co_tm_open_tm_wrt_co in Kip; eauto with lc.
    + match goal with
      | H : open_tm_wrt_co ?a ?g = ?b |- _ => rewrite H; clear H
      end.
      inversion Par1; subst; clear Par1; eauto.
      invert_lc.
      * exists (open_tm_wrt_co a' g_Triv); eauto with lc.
      * exists (open_tm_wrt_co a'2 g_Triv); eauto with lc.
        split; eauto.
        finish_open_co a'.
    + inversion Par1; subst; clear Par1; eauto.
      invert_lc.
      * exists (open_tm_wrt_co a' g_Triv); eauto with lc.
      * exists (open_tm_wrt_co a'1 g_Triv); eauto with lc.
        split; eauto.
        finish_open_co a'.
  - (* capp cong / cbeta *)
    use_size_induction a0 ac Par1 Par2.
    inversion P2; subst; eauto; clear P2.
    + inversion Par2; subst; clear Par2.
      * exists (open_tm_wrt_co a'0 g_Triv); eauto.
      * match goal with
        | [H : a_CApp ?a ?g = ?b |- _ ] => rewrite H
        end.
        exists (open_tm_wrt_co a'1 g_Triv); eauto.
        split; eauto.
        finish_open_co a'0.
    + inversion Par2; subst; clear Par2.
      * invert_lc.
        exists (open_tm_wrt_co a'0 g_Triv); eauto.
        split; eauto.
        match goal with
        | [H :open_tm_wrt_co ?a ?g = ?b |- _ ] => rewrite H
        end.
        pick_fresh c.
        move: (co_subst_co_tm_lc_tm (open_tm_wrt_co a'0 (g_Var_f c))
                                    g_Triv c ltac:(eauto) lc_g_Triv) => Kip.
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in Kip; eauto with lc.
      * match goal with
        | [H : open_tm_wrt_co ?a ?g = ?b |- _ ] => rewrite H
        end.
        exists (open_tm_wrt_co a'2 g_Triv); eauto.
        split; eauto.
        finish_open_co a'0.
    + inversion Par2; subst; clear Par2.
      * match goal with
        | [H : a_CApp ?a ?g = ?b |- _ ] => rewrite H
        end.
        exists (open_tm_wrt_co a'0 g_Triv); eauto.
        split; eauto.
        invert_lc.
        pick_fresh c.
        move: (co_subst_co_tm_lc_tm (open_tm_wrt_co a'0 (g_Var_f c))
                                    g_Triv c ltac:(eauto) lc_g_Triv) => Kip.
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in Kip; auto with lc.
      * match goal with
        | [H : a_CApp ?a ?g = ?b |- _ ] => rewrite H
        end.
        exists (open_tm_wrt_co a'2 g_Triv); eauto.
        split; eauto.
        finish_open_co a'0.
  - (* capp cong / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_CApp ac g_Triv). auto.
  - (* abs cong / abs cong *)
    pick fresh x.
    use_size_induction_open a0 x ac Par1 Par2.
    exists (a_UAbs rho (close_tm_wrt_tm x ac)).
    split; eauto; try solve [apply (@Par_Abs_exists x); eauto].
  - (* pi cong / pi cong *)
    pick fresh x.
    use_size_induction A ac Par1 Par2.
    use_size_induction_open B x bc Par3 Par4.
    exists (a_Pi rho ac R (close_tm_wrt_tm x bc)).
    split; eauto; try solve [apply (@Par_Pi_exists x); eauto].
  - (* cabs cong / cabs cong *)
    pick fresh c.
    use_size_induction_open a0 c ac Par1 Par2.
    exists (a_UCAbs (close_tm_wrt_co c ac)).
    split; eauto; try solve [apply (@Par_CAbs_exists c); eauto].
  - (* cpi cong / cpi cong *)
    use_size_induction A AC Par1 Par2.
    use_size_induction B BC Par3 Par4.
    use_size_induction A1 AC1 Par5 Par6.
    pick fresh c.
    use_size_induction_open a0 c ac Par7 Par8.
    exists (a_CPi (Eq AC BC AC1 R) (close_tm_wrt_co c ac)).
    split; eauto; try solve [apply (@Par_CPi_exists c); eauto].
  - (* fam / fam *)
    have E: (Ax a1 A R = Ax a2 A0 R0). eapply binds_unique; eauto using uniq_toplevel.
    inversion E. subst. clear E.
    have LC: lc_tm a2. apply Toplevel_lc in H. inversion H. auto.
    exists a2. split; eauto.
Qed.

Lemma confluence : forall S D a a1, Good S D -> erased_tm a -> Par S D a a1 -> forall a2, Par S D a a2 -> exists b, Par S D a1 b /\ Par S D a2 b.
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



Ltac binds_notbinds :=
    match goal with
    [ H0 : binds ?c (Ax ?T ?a ?R) toplevel,
      H5 : forall (c : atom) a, not (binds c (Ax ?T a ?R) an_toplevel) |- _  ] =>
      unfold not in H5; unfold toplevel in H0; unfold erase_sig in H0;
      apply binds_map_3 in H0; destruct H0 as (s' & EQ & B);
      destruct s'; simpl in EQ; inversion EQ; subst;
      apply H5 in B; contradiction
      end.


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


Lemma multipar_Pi : forall S D rho R A B, multipar S D A B -> forall A1 A2,
      A = a_Pi rho A1 R A2 -> exists B1 B2, B = (a_Pi rho B1 R B2).
intros S D rho A R B H. induction H. intros. subst. exists A1, A2. auto.
intros. subst.
inversion H; subst; destruct (IHmultipar _ _ eq_refl) as [B1 [B2 EQ]]; auto;
exists B1, B2; auto.
Qed.

Lemma multipar_CPi : forall S D A C, multipar S D A C -> forall A1 A2 A3 R B, A = a_CPi (Eq A1 A2 A3 R) B -> exists B1 B2 B3 C2,
        C = (a_CPi (Eq B1 B2 B3 R) C2).
Proof.
  intros S D A C H. induction H; intros; subst.
  exists A1, A2, A3, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ _ _ _ eq_refl) as [B1 [B2 [C2 EQ]]];
    auto; exists B1, B2, C2; auto.
Qed.


Lemma multipar_UAbs : forall S D rho a b x,
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm b ->
    multipar S D (a_UAbs rho a) b ->
    (exists b2, b = (a_UAbs rho b2))
    \/ (exists a1, exists a2, multipar S D (a_UAbs rho a) (a_UAbs rho a1) /\
               open_tm_wrt_tm a1 (a_Var_f x) = a_App a2 rho (a_Var_f x)).
Proof.
  intros S D rho a b x Fr H. dependent induction H.
  - left. exists a. auto.
  - destruct (Par_Abs_inversion H) as [[a' [EQ _]] | [a' [_ F]]]; subst.
    assert (h0 : x `notin` fv_tm_tm_tm (a_UAbs rho a')). eapply Par_fv_preservation; eauto.
    simpl in h0.
    destruct (IHmultipar _ a' ltac:(auto) eq_refl) as [ [b2 EQ2] | [a1 [a2 [mp1 F2]]] ]; subst; clear IHmultipar.
    left. exists b2. auto.
    right. exists a1, a2. split. eauto. auto.
    right. exists a, a'.
    split. eauto. eauto.
Qed.



Lemma multipar_CAbs : forall S D A C, multipar S D A C -> forall A1 A2 A3 R B, A = a_CAbs (Eq A1 A2 A3 R) B -> exists B1 B2 B3 C2,
        C = (a_CAbs (Eq B1 B2 B3 R) C2).
Proof.
  intros S D A C H. induction H; intros; subst.
  exists A1, A2, A3, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ _ _ _ eq_refl) as [B1 [B2 [C2 EQ]]];
    auto; exists B1, B2, C2; auto.
Qed.

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
  | [ SIDE : multipar _ _ (a_Pi _ _ _ _) _ |- _ ] =>
    destruct (multipar_Pi SIDE eq_refl) as [b1' [b2' EQ]]
  | [ SIDE : multipar _ _ (a_CPi ?phi _) _ |- _ ] =>
    try (destruct phi); destruct (multipar_CPi SIDE eq_refl)
      as (B1' & B2' & C1' & C2' &  EQ)
  | [ SIDE : multipar _ _ (a_Const ?T) _ |- _ ] =>
    apply multipar_Const in SIDE; auto; rename SIDE into EQ
  end.



Lemma join_consistent : forall S D a b, joins S D a b -> consistent a b.
Proof.
  intros.
  all: destruct H as (TT & Es & Ea & Eb & MSL & MSR).
  all: move: (erased_lc Ea) => lc_a.
  all: move: (erased_lc Eb) => lc_b.
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

  all: try multipar_step MSL EQ1.
  all: try multipar_step MSR EQ2.
  all: try solve [rewrite EQ1 in EQ2; inversion EQ2; try inversion H; auto].
  all: try solve [eapply consistent_a_Step_R; [auto | intros h0; inversion h0; unfold not in NP; eauto]].
  all: try solve [eapply consistent_a_Step_L; [auto | intros h0; inversion h0; unfold not in NP; eauto]].

  - destruct (multipar_Pi MSL eq_refl) as (B1 & B2 & EQ).
    destruct (multipar_Pi MSR eq_refl) as (B1' & B2' & EQ').
    subst.
    inversion EQ. inversion EQ'.
    subst. econstructor; eauto.
    inversion lc_a. auto.
    inversion lc_b. auto.
  - destruct phi.
    destruct (multipar_CPi MSL eq_refl) as (B1 & B2 & EQ).
    destruct (multipar_CPi MSR eq_refl) as (B1'' & B2'' & EQ').
    subst.
    inversion EQ. inversion EQ'.
    subst. econstructor; eauto.
    inversion lc_a. auto.
    inversion lc_b. auto.

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
  - intros. exists a2. split; eauto.
  - intros. destruct (confluence Es E H H1) as [d [L R]].
      inversion Es.
      assert (erased_tm b). eapply Par_erased_tm; eauto.
      destruct (IHmultipar H4 d) as [e [LL RR]]; auto.
      exists e. split; eauto.
Qed.

(*

a -->  b -->* c    d - by prior lemma
|      |      |    e - by induction.
v      v      v
*      *      *
a2 --> d -->* e

*)

Lemma multipar_confluence : forall S D a a1, Good S D -> erased_tm a -> multipar S D a a1
-> forall a2, multipar S D a a2 -> exists b, multipar S D a1 b /\ multipar S D a2 b.
Proof.
  intros S D a a1 Es Ea MP. induction MP.
intros.
 - exists a2. split. eauto. eauto.
 - intros.
   destruct (multipar_confluence_helper Es Ea H0 H) as [d [L R]].
   inversion Es.
   assert (Eb : erased_tm b). eapply Par_erased_tm; eauto.
   destruct (IHMP Eb d) as [e [LL RR]]; auto.
   exists e. split; eauto.
Qed.

Lemma multipar_append : forall S D a b c, multipar S D a b -> multipar S D b c -> multipar S D a c.
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

Lemma join_symmetry: forall S D a b, joins S D a b -> joins S D b a.
Proof.
  intros S D a b H.
  destruct H as [ac h0].
  split_hyp.
  exists ac; eauto.
Qed.


Definition extends (G G2 : context) := exists G1, G = G1 ++ G2.

Lemma multipar_lc2: forall G D a1 a2, lc_tm a1 -> multipar G D a1 a2 -> lc_tm a2.
  induction 2; eauto.
  apply IHmultipar.
  eapply Par_lc2; apply H0.
Qed.


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
    - destruct phi. inversion H. subst. auto.
    - eapply Forall_forall in H; eauto.
      simpl in H. auto.
  + intros c1 c2. intros.
    assert (c <> c1). fsetdec.
    apply binds_cons_1 in H.
    destruct H as [[EQ _] | BI1]. fsetdec.
    edestruct (M c1) as (C & P1 & P2); eauto.
    exists C.
    repeat split;
      apply context_Par_irrelevance with (G1 := G)(D1 := D)(D2 := D); auto; try fsetdec;
        unfold sub_Axiom;
        intros;
        apply binds_cons; auto.
Qed.

Hint Resolve Good_NoAssn.

Hint Resolve multipar_context_independent.

Lemma Good_add_tm: forall G D x A R,
    erased_tm A -> Good G D -> Good ((x, Tm A R)::G ) D.
Proof.
  intros G D x A R E H.
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
  + intros c1 A1 B1 T1 R0 BI1 I1.
  destruct H as (Es & M).
  apply binds_cons_1 in BI1.
  destruct BI1 as [[_ EQ] | BI1]. inversion EQ.
  edestruct (M c1) as (C & P1 & P2); eauto.
  exists C. repeat split;
    apply context_Par_irrelevance with (G1 := G)(D1 := D); auto; try fsetdec;
    unfold sub_Axiom;
    intros;
    apply binds_cons; auto.
Qed.

Lemma Good_add_tm_2: forall G D x A R, x `notin` dom G -> erased_tm A -> Good G D -> Good ((x, Tm A R)::G ) (add x D).
Proof.
  intros G D x A R FR E H.
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
  + intros c1 A1 B1 T1 R0 BI1 I1.
  destruct H as (Es & M).
  apply binds_cons_1 in BI1.
  destruct BI1 as [[_ EQ] | BI1]. inversion EQ.
  edestruct (M c1) as (C & P1 & P2); eauto.
  move: (binds_In _ c1 _ _ BI1) => b0. fsetdec.
  exists C. repeat split;
    apply context_Par_irrelevance with (G1 := G)(D1 := D); auto; try fsetdec;
    unfold sub_Axiom;
    intros;
    apply binds_cons; auto.
Qed.




Lemma multipar_app_left:
  forall rho a a' c' S D, lc_tm a -> multipar S D a' c' -> multipar S D (a_App a rho a') (a_App a rho c').
Proof.
  induction 2; eauto; try done.
Qed.

Lemma multipar_capp_left: forall a a' S D, multipar S D a a' -> multipar S D (a_CApp a g_Triv) (a_CApp a' g_Triv).
Proof.
  induction 1; eauto; try done.
  Unshelve. auto.
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

Lemma multipar_app_lr: forall rho a a' c c' S D, lc_tm a -> lc_tm a' -> multipar S D a c -> multipar S D a' c' -> multipar S D (a_App a rho a') (a_App c rho c').
Proof.
  induction 3; eauto; try done.
  intros H1.
  apply multipar_app_left; auto.
  intros H3.
  apply (@mp_step S D _ (a_App b rho a')); eauto.
  (have: lc_tm b by eapply Par_lc2; eauto); eauto.
  Unshelve. auto. auto.
Qed.

Lemma join_app: forall rho a a' b b' S D, joins S D a b -> joins S D a' b' -> joins S D (a_App a rho a') (a_App b rho b').
Proof.
  unfold joins.
  intros rho a a' b b' S D H H0.
  destruct H as [ac h0].
  destruct H0 as [ac' h1].
  split_hyp.
  exists (a_App ac rho ac').
  repeat split; eauto.
  apply multipar_app_lr; auto; try solve [eapply erased_lc; eauto].
  apply multipar_app_lr; auto; try solve [eapply erased_lc; eauto].
Qed.


Lemma multipar_UAbs_exists :  ∀ (x : atom) (G : context) (D : available_props)
       (rho : relflag) (a a' : tm),
    x `notin` fv_tm_tm_tm a
       → multipar G D (open_tm_wrt_tm a (a_Var_f x)) a'
         → multipar G D (a_UAbs rho a) (a_UAbs rho (close_tm_wrt_tm x a')).
Proof.
  intros.
  dependent induction H0.
  autorewrite with lngen. auto.
  eapply mp_step.
  eapply Par_Abs_exists with (x:=x); eauto.
  eapply IHmultipar; eauto. autorewrite with lngen. auto.
  autorewrite with lngen. auto.
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
  move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a1 (a_Var_f x)) => h0. fsetdec.
  eapply (@erased_a_Abs L2).
  intros.
  move: (H0 x H1) => RC. inversion RC.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a2 (a_Var_f x)) a_Bullet x); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
  move: (fv_tm_tm_tm_open_tm_wrt_tm_lower a2 (a_Var_f x)) => h0. fsetdec.

  eapply (multipar_iapp _ _ H). eauto.
  eapply (multipar_iapp _ _ H0). eauto.
  Unshelve. eauto. eauto.
Qed.

Lemma multipar_App_destruct : forall S D rho a1 a2 c,
    multipar S D (a_App a1 rho a2) c ->
    (exists a1' a2',
        multipar S D (a_App a1 rho a2) (a_App (a_UAbs rho a1') rho a2') /\
        multipar S D a1 (a_UAbs rho a1') /\
        multipar S D a2 a2' /\
        multipar S D (open_tm_wrt_tm a1' a2') c) \/
    (exists a1' a2',
        multipar S D (a_App a1 rho a2) (a_App a1' rho a2') /\
        multipar S D a1 a1' /\
        multipar S D a2 a2').
Proof.
  intros. dependent induction H.
  right.
  exists a1, a2. split; auto.
  inversion H.
  + subst. eauto.
  + subst. left.
    exists a', b'. split; auto.
    assert (lc_tm a1). eapply Par_lc1. eauto.
    assert (lc_tm a2). eapply Par_lc1. eauto.
    eapply multipar_app_lr; eauto.
    split.
    eapply mp_step; eauto.
    split; eauto.
  +
    assert (lc_tm a1). eapply Par_lc1. eauto.
    assert (lc_tm a2). eapply Par_lc1. eauto.
    subst. destruct (IHmultipar rho a' b') as [[a1' [a2' [P1 [P2 [P3 P4]]]]] |
                                                [a1' [a2' [P1 [P2 P3]]]]] ; auto.
    ++ clear IHmultipar. left.
       exists a1', a2'.
       repeat split; eauto.
    ++ clear IHmultipar. right.

       exists a1', a2'.
       repeat split; eauto.
Unshelve.
all: exact S.
Qed.


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
      (have: lc_tm a1 by eapply erased_lc; eauto) => lc1;
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K;
      eauto;try solve [eapply multipar_lc2; eauto | eapply multipar_lc2; eauto];
      simpl in K;
      destruct eq_dec; try congruence;
      repeat rewrite tm_subst_tm_tm_fresh_eq in K; auto
   end.
Ltac multipar_CPi c :=
  apply multipar_CPi_exists; auto;
  [ apply (lc_a_CPi_exists c); try constructor; apply erased_lc; auto |
    eapply multipar_context_independent; eauto].


Lemma consistent_mutual:
  (forall S a A R,   Typing S a A R -> True) /\
  (forall S phi,   PropWff S phi -> True) /\
  (forall S D p1 p2, Iso S D p1 p2 -> Good S D -> (forall A1 B1 T1 A2 B2 T2 R1 R2, p1 = Eq A1 B1 T1 R1 -> p2 = Eq A2 B2 T2 R2 -> (joins S D A1 A2 /\ joins S D B1 B2 /\ joins S D T1 T2))) /\
  (forall S D A B T R,   DefEq S D A B T R -> Good S D -> joins S D A B) /\
  (forall S,       Ctx S -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; eauto; try done.
  - intros G D A1 B1 A R A2 B2 d H d0 H0 H1 A0 B0 T1 A3 B3 T2 R1 R2 H2 H3.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    repeat split; eauto.
    exists T2; eauto.
    have et: erased_tm T2.
    apply DefEq_regularity in d.
    pose K := (second typing_erased_mutual) _ _ d A0 A3 T2 R2.
    apply K; auto.
    repeat split; auto.
    have C: Ctx G by eauto.
    unfold erased_context.
    apply Forall_forall.
    intros. destruct x. destruct s.
    apply binds_to_Typing in H2.
    apply Typing_erased in H2.
    eapply erased_Tm. auto. auto.
    destruct phi. apply binds_to_PropWff in H2.
    inversion H2.
    eapply erased_Co; eauto using Typing_erased. auto.
  - intros G D A1 A2 A R B d H p H0 p0 H1 H2 A0 B1 T1 A3 B2 T2 R1 R2 H3 H4.
    inversion H4; subst; clear H4.
    inversion H3; subst; clear H3.
    inversion p; subst.
    inversion H2.
    have lc1: lc_tm A0 by eapply Typing_lc in H7; split_hyp; eauto.
    have lc2: lc_tm B1 by eapply Typing_lc in H9; split_hyp; eauto.
    repeat split; eauto.
    + exists A0.
      repeat split; eauto; try solve [eapply (Typing_erased); eauto]; eauto.
    + exists B1.
      repeat split; eauto; try solve [eapply (Typing_erased); eauto]; eauto.
  - intros G D5 phi1 phi2 B1 B2 R d H H0 A1 B0 T1 A2 B3 T2 R1 R2 H1 H2.
    destruct phi1.
    destruct phi2.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    destruct H as [Bc h0]; auto.
    split_hyp.
    pose K1 := multipar_CPi H3 eq_refl.
    destruct K1 as [B1' [B2' [B3' [Bc' h0]]]].
    subst.
    pose K1 := multipar_CPi_phi_proj H3.
    pose K2 := multipar_CPi_phi_proj H4.
    split_hyp.
    repeat split; eauto.
    + exists B1'.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      repeat split; eauto.
    + exists B2'.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      repeat split; eauto.
    + exists B3'.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      repeat split; eauto.
  - (* assn *)
    intros G D a b A R c c0 H b0 i H0.
    destruct H0 as (Es & M).
    edestruct (M c); eauto.
    split_hyp.
    unfold erased_context in Es.
    move:
      (@Forall_forall _ (λ (p : (atom*sort)), let (_, s) := p in erased_sort s) G) => [h0 _].
    move: (h0 Es _ b0) => h1.
    inversion h1.
    unfold joins. exists x. repeat split; eauto.
  - (* refl *)
    intros G D a A R t H H0.
    inversion H0.
    unfold joins. exists a.
    repeat split; try solve [eapply (Typing_erased); eauto]; eauto.
  - (* symmetry *)
    intros G D a b A R d H H0.
    unfold joins in *. destruct H as [c [L R0]]; auto.
    exists c. tauto.
  - (* transitivity *)
    intros. eapply join_transitive; auto.
  - (* confluence *)
    intros G. intros.
    inversion H1.
    unfold joins in *. subst.
    have p: Par G D a1 a2.
    { inversion b.
      eapply Par_Beta; eauto 2. eauto using Value_lc.
      eapply Par_CBeta; eauto 2.
      eapply Par_Axiom; eauto 2.
      }
    destruct (confluence H1 (Typing_erased t) p p) as [ac [h0 h1]].
    exists ac; eauto.
    pose K2 := Typing_erased t0.
    repeat split; eauto.
    eapply Typing_erased; eauto.
  - (* pi-cong *)
    intros L G D rho A1 R B1 A2 B2 R' d H d0 H0 _ _ t H1 t0 H2 S H3.
    inversion H3.
    have e0: erased_tm (a_Pi rho A1 R B1). eapply Typing_erased; eauto.
    inversion e0. subst.
    pose Ih1 := H H3.
    pick fresh x for (L \u (fv_tm_tm_tm B1) \u (fv_tm_tm_tm B2) \u dom G).
    assert (G' : Good ([(x, Tm A1 R)] ++ G) D).
    { apply Good_add_tm; auto. }
    have: x `notin` L; auto => fr.
    pose Ih2 := H0 x fr G'.
    destruct H as [A'' h1]; auto; subst.
    destruct Ih2 as [B'' h2].
    split_hyp.
    exists (a_Pi rho A'' R (close_tm_wrt_tm x B'')); eauto.
    repeat split; eauto 1.
    + apply (@erased_a_Pi L); try solve [apply h2; auto]; try solve [apply h1; auto]; eauto.
      intros x0 h4.
      assert (G'' : Good ([(x0, Tm A1 R)] ++ G) D).
      apply Good_add_tm; auto.
      pose Ih2 := H0 x0 h4 G''.
      destruct Ih2 as [C'' h3]; eauto.
      apply h3.
    + apply multipar_Pi_exists; auto.
      apply (lc_a_Pi_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
    + apply multipar_Pi_exists; auto.
      apply (lc_a_Pi_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
  - (* abs-cong *)
    intros L G D rho b1 b2 A1 R B R' IHDefEq H1 t _ S RC1 RC2 GOOD.
    inversion GOOD.
    have e0: erased_tm A1. eapply Typing_erased; eauto.
    pick fresh x for (L \u (fv_tm_tm_tm b1) \u (fv_tm_tm_tm b2)).
    assert (G' : Good ([(x, Tm A1 R)] ++ G) D).
    apply Good_add_tm; auto.
    have: x `notin` L; auto => fr.
    pose Ih2 := H1 x fr G'.
    destruct Ih2 as [B'' h2].
    split_hyp.
    exists (a_UAbs rho (close_tm_wrt_tm x B'')); eauto.
    repeat split; eauto 1.
    + apply (@erased_a_Abs L); try solve [apply h2; auto]; try solve [apply h1; auto]; eauto.
      intros x0 h4.
      assert (G'' : Good ([(x0, Tm A1 R)] ++ G) D).
      apply Good_add_tm; auto.
      pose Ih2 := H1 x0 h4 G''.
      destruct Ih2 as [C'' h3]; eauto.
      apply h3.
    + apply (@erased_a_Abs L); try solve [apply h2; auto]; try solve [apply h1; auto]; eauto.
      intros x0 h4.
      assert (G'' : Good ([(x0, Tm A1 R)] ++ G) D).
      apply Good_add_tm; auto.
      pose Ih2 := H1 x0 h4 G''.
      destruct Ih2 as [C'' h3]; eauto.
      apply h3.
    + apply multipar_Abs_exists; auto.
      apply (lc_a_UAbs_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
    + apply multipar_Abs_exists; auto.
      apply (lc_a_UAbs_exists x); apply erased_lc; auto.
      eapply multipar_context_independent; eauto.
  - intros G D a1 a2 b1 b2 d R' H R d0 H0 p H1 H2.
    apply join_app; auto.
  - intros G D a1 b1 B a R' A R d H t H0 H1.
    inversion H1.
    apply join_app; auto.
    exists a_Bullet. repeat split; eauto.
  - intros G D A1 A2 R rho B1 B2 R' H IHDefEq GOOD.
    inversion GOOD.
    destruct IHDefEq; auto.
    split_hyp.
    pose K1 := multipar_Pi H5 eq_refl.
    destruct K1 as [A' [B' h0]].
    subst.
    inversion H3; inversion H4; subst.
    apply multipar_Pi_A_proj in H5.
    apply multipar_Pi_A_proj in H6.
    exists A'; eauto.
    apply erased_lc; eauto.
    apply erased_lc; eauto.
  - intros G D B1 a1 B2 a2 R' rho A1 R A2 H IHDefEq1 H0 IHDefEq2 GOOD.
    inversion GOOD.
    destruct IHDefEq1; auto.
    destruct IHDefEq2 as [ac h0]; auto.
    split_hyp.
    pose K1 := multipar_Pi H11 eq_refl.
    destruct K1 as [A' [B' h0]].
    subst.
    inversion H9.
    inversion H10; subst.
    apply (multipar_Pi_B_proj) in H11.
    apply (multipar_Pi_B_proj) in H12.
    destruct H11 as [L1 h9].
    destruct H12 as [L2 h10].
    pick_fresh x.
    exists (open_tm_wrt_tm B' ac).



  repeat split; eauto.
    + subst_tm_erased_open x.
    + subst_tm_erased_open x.
    + multipar_subst_open x.
    + multipar_subst_open x.
  - (* cpi-cong *)
    intros L G D phi1 A phi2 B R H hi0 H1 IHDefEq H2 _ _ t _ _ GOOD .
    destruct phi1.
    destruct phi2.
    pick_fresh c.
    match goal with
      | [ H : Iso G D (Eq a b A0 R0) (Eq a0 b0 A1 R1) |- _ ] =>
        destruct (hi0 GOOD a b A0 a0 b0 A1 R0 R1) as [hi1 [hi2 hi3]]; auto
    end.
    have EC : erased_sort (Co (Eq a b A0 R0)).
    { inversion H2. apply erased_Co; eapply Typing_erased; eauto. }
    destruct (IHDefEq c) as [Ac h1]; eauto.
    + apply Good_NoAssn; auto.
    + split_hyp.
      unfold joins in *.
      destruct hi1 as [Aco h0'].
      destruct hi2 as [Bco h1'].
      destruct hi3 as [Tco h2'].
      split_hyp.
      exists (a_CPi (Eq Aco Bco Tco R0) (close_tm_wrt_co c Ac)); eauto.
      repeat split; eauto 1.
      * apply (@erased_a_CPi (L \u D)); eauto.
        intros c0 Hi5.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * apply (@erased_a_CPi (L \u D)); eauto.
        intros c0 Hi5.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * (* Ltac context_independence c := *)
     (* eapply multipar_context_independent; eauto.
        intros x; intros; assert (x <> c); [fsetdec|
        match goal with
          [ H23 : binds ?x (Co (Eq (a_Const ?F) ?a ?A4 ?R)) ([(c, Co (Eq ?A0 ?B0 ?A1 ?R'))] ++ ?G) |- _ ] =>
              simpl in H23;
              edestruct (binds_cons_1 _ x c _ _ G H23) as [[h0 h1] | h2];
              [contradiction| auto]
        end]. *)
        multipar_CPi c.
      * admit. (* multipar_CPi c. *)
  - intros L G D a b phi1 B R hi0 IHDefEq H1 _ GOOD.
    destruct phi1.
    pick_fresh c.
    have EC : erased_sort (Co (Eq a0 b0 A R0)).
    { inversion H1. apply erased_Co; eapply Typing_erased; eauto. }
    inversion GOOD.
    destruct (IHDefEq c) as [Ac h1]; auto.
    + apply Good_NoAssn; auto.
    + split_hyp.
      unfold joins in *.
      exists (a_UCAbs (close_tm_wrt_co c Ac)); eauto.
      split_hyp.
      repeat split; eauto 1.
      * apply (@erased_a_CAbs (L \u D)); eauto.
        intros c0 Hi6.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * apply (@erased_a_CAbs (L \u D)); eauto.
        intros c0 Hi5.
        destruct (IHDefEq c0) as [Ac' h2']; auto; subst.
        apply Good_NoAssn; auto.
        apply h2'.
      * apply multipar_CAbs_exists; auto.
        apply (lc_a_UCAbs_exists c); try constructor; apply erased_lc; auto.
        eapply multipar_context_independent; eauto.
      * apply multipar_CAbs_exists; auto.
        apply (lc_a_UCAbs_exists c); try constructor; apply erased_lc; auto.
        eapply multipar_context_independent; eauto.
  - intros G D a1 b1 B R' a b A R d H p H0 H1.
    apply join_capp; auto.
  - intros G D B1 B2 R0 A1 A2 A R A1' A2' A' R' H0 IHDefEq hi1 IHDefEq2 hi0 IHDefEq3 GOOD.
    destruct IHDefEq as [Ac h0]; eauto.
    split_hyp.
    inversion GOOD.
    match goal with
      [ H1 : erased_tm (a_CPi (Eq A1 A2 A R) B1),
        H2 : erased_tm (a_CPi (Eq A1' A2' A' R') B2),
        H3 :  multipar G D (a_CPi (Eq A1 A2 A R) B1) Ac,
        H4 : multipar G D (a_CPi (Eq A1' A2' A' R') B2) Ac |- _ ] =>
      pose K1 := multipar_CPi H3 eq_refl;
      destruct K1 as [B1' [B2' [B3' [Bc' h0]]]];
      subst;
      inversion H1;
      inversion H2; subst;
      apply multipar_CPi_B_proj in H3;
      apply multipar_CPi_B_proj in H4;
      destruct H3 as [L1 H3];
      destruct H4 as [L2 H4]
    end.
    pick_fresh c.
    exists (open_tm_wrt_co Bc' g_Triv).
    have: c `notin` L; auto => h.
    have: c `notin` L0; auto => h0.
    repeat split; eauto 1.
    + Ltac erased_open_tm_wrt_co c B1 :=
        let K:= fresh in
        match goal with
        [ h : c `notin` ?L, H11 :  ∀ c : atom, c `notin` ?L → erased_tm (open_tm_wrt_co B1 (g_Var_f c)) |- _ ] =>
        pose K := subst_co_erased c lc_g_Triv (H11 c h);
        clearbody K;
        repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; auto;
        simpl in K;
        destruct eq_dec; try congruence;
        rewrite co_subst_co_tm_fresh_eq in K; auto
        end.
      erased_open_tm_wrt_co c B1.
    + erased_open_tm_wrt_co c B2.
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
  - intros G D A' B' a' R' A B a R d H i H0 H1.
    destruct (H0 H1 A B a A' B' a' R R'); auto.
    move: (H H1) => h0.
    split_hyp.
    have h1 : joins G D A' B; eauto.
    apply join_transitive with (b := A); eauto.
    apply join_symmetry; auto.
    apply join_transitive with (b := B); eauto.
  - intros G D A A' R a b a' b' i H H0.
    destruct (H H0 a b A a' b' A' R R); auto.
    destruct H2; auto.
    Unshelve. all: auto.
Admitted.

Lemma consist_Pi_rEq : forall T1 T2, consistent T1 T2 ->
               forall rho A1 A2 R1 R2 B1 B2,
               lc_tm A1 -> lc_tm (a_Pi rho A1 R1 B1) ->
               lc_tm A2 -> lc_tm (a_Pi rho A2 R2 B2) ->
               T1 = a_Pi rho A1 R1 B1 -> T2 = a_Pi rho A2 R2 B2 ->
               R1 = R2.
Proof. intros T1 T2 H. induction H; intros.
         - inversion H3.
         - inversion H7. inversion H8. subst. auto.
         - inversion H7.
         - subst. assert False. apply H0. eauto. inversion H5.
         - subst. assert False. apply H0. eauto. inversion H5.
Qed.

Lemma defEq_Pi_rEq : forall rho A1 A2 R1 R2 B1 B2 R' G D,
             Good G D ->
             DefEq G D (a_Pi rho A1 R1 B1) (a_Pi rho A2 R2 B2) a_Star R'
             -> R1 = R2.
Proof. intros. assert (H' := H0).
       apply lc_mutual in H0.
       inversion H0 as [H1 [H2 _]].
       eapply consist_Pi_rEq. eapply join_consistent.
       eapply consistent_mutual; eauto. inversion H1.
       apply H5. apply H1. inversion H2. apply H5. 
       apply H2. auto. auto.
Qed.

Lemma consistent_defeq: forall S D A B T R,   DefEq S D A B T R -> Good S D -> joins S D A B.
Proof.
  apply consistent_mutual.
Qed.

(* ------------------------------------------------------- *)

Lemma no_aAbs : forall G rho A' a A R R', Typing G (a_Abs rho A' R' a) A R -> False.
Proof.
  intros. dependent induction H. by apply: IHTyping. by apply: IHTyping1.
Qed.

Lemma no_aCAbs : forall G A' a A R, Typing G (a_CAbs A' a) A R -> False.
Proof.
  intros. dependent induction H. by apply: IHTyping. by apply: IHTyping1.
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
  (forall x A R, binds x (Tm A R) G -> x `notin` fv_tm a) /\ Good G D.

Lemma irrelevant_Good : forall G D a, irrelevant G D a -> Good G D.
intros. inversion H.
auto.
Qed.



(* When we have a defeq in the context between two value types, show that it
   can't happen. *)
Ltac impossible_defeq :=
  let h0 := fresh in
  let VT := fresh in
  let VT2 := fresh in
  match goal with
  | [ H : DefEq ?G (dom ?G) ?B ?A ?C ?R |- _ ] =>
    pose h0:= H; clearbody h0;
    apply consistent_defeq in h0; eauto;
    [apply join_consistent in h0;
     destruct (DefEq_lc H) as (l0 & l1 & l2); inversion l0; inversion l1; subst;
     have VT: value_type A; eauto;
     have VT2 : value_type B; eauto;
     inversion h0; subst;
     eauto; try done | eapply irrelevant_Good; eauto]
  end.


Lemma canonical_forms_Star : forall G a R, irrelevant G (dom G) a ->
    Typing G a a_Star R -> Value a -> value_type a.
Proof.
  intros G a R IR H V. induction V; auto.
  - subst. assert False. eapply no_aAbs. eauto 2. done.
  - subst. apply invert_a_UAbs in H; eauto.
    destruct H as [A1 [B2 [R0 [H _]]]].
    impossible_defeq.
  - subst. apply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & DE & TA1 & TA2).
    impossible_defeq.
  - subst. assert False. eapply  no_aAbs. eauto 2. done.
  - subst.  assert False. eapply no_aCAbs. eauto 2. done.
  - subst. apply invert_a_UCAbs in H; eauto.
    destruct H as [a0 [b [T [R1 [B1 [R2 [_ [H _]]]]]]]].
    impossible_defeq.
Qed.



Lemma DefEq_Star: forall A G D R, Good G D -> value_type A -> DefEq G D A a_Star a_Star R -> A = a_Star.
Proof.
  intros A G D R Good H0 H.
  apply consistent_defeq in H; eauto.
  apply join_consistent in H.
  inversion H;  eauto; subst; try done.
Qed.

Lemma canonical_forms_Pi : forall G rho a A R B R', irrelevant G (dom G) a ->
    Typing G a (a_Pi rho A R B) R' -> Value a ->
    (exists a1, a = a_UAbs rho a1).
Proof.
  intros G rho a A R B R' IR H H0.
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
    destruct H as (A1 & A2 & R0 & H & _); eauto.
    impossible_defeq.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & B1 & R0 & H & _); eauto.
    impossible_defeq.
  - assert False. eapply no_aAbs. eauto 2. done.
  - assert False. eapply no_aCAbs. eauto 2. done.
  - eapply invert_a_UCAbs in H; eauto.
    destruct H as [a [b [T [R1 [B1 [_ [_ [H _]]]]]]]]; eauto.
    impossible_defeq.
Qed.

Lemma canonical_forms_CPi : forall G a phi B R, irrelevant G (dom G) a ->
    Typing G a (a_CPi phi B) R -> Value a ->
    (exists a1, a = a_UCAbs a1).
Proof.
  intros G a phi B R IR H H0.
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
    destruct H as [A1 [A2 [R' [H _]]]]; eauto.
    impossible_defeq.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [R' [H _]]]]; eauto.
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
        intros x A0 R0 B0;  apply h0 in B0; simpl in B0; fsetdec.

Lemma notin_sub : forall x a b, x `notin` a -> b [<=] a -> x `notin` b.
  intros. fsetdec.
Qed.



(*
   The progress lemma is stated in terms of the reduction_in_one relation,
   which is a subrelation of the Par relation.
*)

Lemma progress : forall G a A R, Typing G a A R ->
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
      move: (H2 x H4) => h0.
      inversion h0. subst.
      destruct (H0 x H4) as [V | [a' T]].
      { move: (H x H4) => h1.
      unfold irrelevant in *.
      destruct IR as [h2 h3].
      have ctx: (Ctx ([(x, Tm A R)] ++ G)) by eauto.
      move: (Ctx_uniq ctx) => u. inversion u. subst.
      split. intros x0 A0 R0 b0.
      apply binds_cons_uniq_1 in b0. destruct b0.
      ++ split_hyp. subst. auto.
      ++ split_hyp.
         move: (h2 _ _ _ H6) => fr. simpl in fr.
         eapply notin_sub; [idtac|eapply fv_tm_tm_tm_open_tm_wrt_tm_upper].
         simpl.
         fsetdec.
      ++ eauto.
      ++ simpl. eapply Good_add_tm_2; eauto using Typing_erased. }
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
Qed.




End ext_consist.

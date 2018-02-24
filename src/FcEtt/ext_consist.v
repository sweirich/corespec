
Require Import Omega.

Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ett_erased.
Require Export FcEtt.ett_par.
Require Import FcEtt.ext_wf.
Require Import FcEtt.ext_invert.
Require Import FcEtt.ext_red_one.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

 Definition Good (G : context) (D : available_props):=
  forall c1 A B1 T1 R,
    binds c1 (Co (Eq A B1 T1 R)) G
    -> c1 `in` D
    -> exists C, Par (ctx_to_rctx G) A C R /\ Par (ctx_to_rctx G) B1 C R.

(* ---------------------------------------- *)

Lemma open2 :
  forall x b b' W a a' R R',
    x `notin` fv_tm_tm_tm a' \u fv_tm_tm_tm a \u dom W ->
    Par ([(x,R)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)) R' ->
    Par W b b' R ->
    Par W (open_tm_wrt_tm a b) (open_tm_wrt_tm a' b') R'.
Proof.
  intros x b b'. intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ b')] (tm_subst_tm_tm_intro x); auto.
  replace W with (nil ++ W); auto.
  eapply subst3; eauto.
Qed.

Lemma open3 :
  forall c L W a a' R',
    c `notin` fv_co_co_tm a' \u fv_co_co_tm a \u dom W \u L ->
    Par W (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)) R' ->
    Par W (open_tm_wrt_co a g_Triv) (open_tm_wrt_co a' g_Triv) R'.
Proof.
  intros x L. intros.
  rewrite (co_subst_co_tm_intro x); auto.
  rewrite [(_ a' g_Triv)] (co_subst_co_tm_intro x); auto.
  replace W with (nil ++ W); auto.
  eapply subst4; eauto.
Qed.


Lemma a_Pi_head : forall W b A R rho B R',
    Par W (a_Pi rho A R B) b R' -> exists A' B' L,
      b = a_Pi rho A' R B' /\ Par W A A' R /\
      (forall x, x `notin` L -> 
        Par([(x,R)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) 
                               (open_tm_wrt_tm B' (a_Var_f x)) R').
Proof.
  intros. inversion H. subst.
  inversion H0. subst.  exists A , B, L. split; auto.
  subst. exists A', B', L.  split; auto.
Qed.

Lemma Par_Abs_inversion : forall W a b rho R R',
    Par W (a_UAbs rho R a) b R' ->
    exists a', b = (a_UAbs rho R a') /\
          forall x, x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm a' \u dom W ->
         Par ([(x,R)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm a' (a_Var_f x)) R'.

Proof.
  intros W a a' rho R R' P.
  inversion P; subst.
  + inversion H. subst. exists a. split. reflexivity.
    intros. econstructor. eapply rctx_uniq in H.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    replace ([(x,R)] ++ W) with (nil ++ ([(x,R)] ++ W)); auto.
    eapply subst_tm_erased. simpl_env.
    eapply erased_app_rctx; simpl_env.
    solve_uniq. auto. econstructor. solve_uniq. auto. auto.
  + exists a'0. split. auto. intros. eapply Par_rctx_uniq in P.
    pick fresh y.
    rewrite (tm_subst_tm_tm_intro y); eauto.
    rewrite (tm_subst_tm_tm_intro y a'0); eauto.
    replace ([(x,R)] ++ W) with (nil ++ ([(x,R)] ++ W)); auto.
    eapply subst2. simpl_env.
    eapply par_app_rctx; simpl_env.
    solve_uniq. auto. econstructor. solve_uniq. auto. auto.
Qed.

Lemma Par_Cong_inversion : forall W a1 a2 R R',
      Par W (a_Conv a1 R' g_Triv) a2 R ->
      exists a3, a2 = a_Conv a3 R' g_Triv.
Proof. intros. inversion H; subst.
       - exists a1; auto.
(*       - exists a3; auto.
       - exists a3; auto. *)
Qed.

(* -------------------------------------------------------------------------------- *)

Ltac try_refl :=
  try match goal with
      | [ P2 : Par _ ?b |- _ ] =>
        exists b; assert (lc_tm b); try eapply Par_lc2; eauto; try split; eauto; fail
      end.


Ltac invert_equality :=
  match goal with
  | [ H : _ = _ |- _ ] =>
    inversion H
  end.

  Ltac try_Refl_left :=
  try match goal with
      | [ P1 : Par _ ?b ?b _,
          P2 : Par _ ?b ?c _ |-
          exists cc:tm, Par _ ?b cc _ /\ Par _ ?c cc _ ] =>
        exists c; split; auto; 
        apply Par_Refl; eapply Par_erased_tm_snd;
        eauto; fail
      end.

  Ltac try_Refl_right :=
  try match goal with
      | [ P1 : Par _ ?b ?c _,
          P2 : Par _ ?b ?b _ |- 
          exists cc:tm, Par _ ?c cc _ /\ Par _ ?b cc _ ] =>
        exists c; split; auto; 
        apply Par_Refl; eapply Par_erased_tm_snd;
        eauto; fail
      end.

Ltac use_size_induction a conf L1 L2 :=
  match goal with
  | [   IH : forall y: nat, ?T,
        H1 : Par ?W a ?b0 ?R,
        H2 : Par ?W a ?b1 ?R |- _ ] =>
      move: (@IH (size_tm a) ltac:(omega) a ltac:(auto) _ _ _ H1 _ H2) => 
      [ conf [L1 L2]]
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
              → Par ?W (?open_tm_wrt_tm a0 (?a_Var_f x)) ?b ?R,
             H4: ∀ x : atom,
                 x `notin` ?L0
                 → Par ?W (?open_tm_wrt_tm a0 (?a_Var_f x)) ?c ?R
                        |- _ ] =>
    move: (H x ltac:(auto)) => h0; clear H;
    move: (H4 x ltac:(auto)) => h1; clear H4;
    move: (size_tm_open_tm_wrt_tm_var a0 x) => EQ1;
    move: (size_tm_open_tm_wrt_co_var a0 x) => EQ2;

    use_size_induction (open_tm_wrt_tm a0 (a_Var_f x)) ac Par1 Par2;
    clear h0; clear h1; clear EQ1; clear EQ2
    end.


Lemma confluence_size : forall n a, size_tm a <= n ->  forall W a1 R, Par W a a1 R -> forall a2, Par W a a2 R -> exists b, Par W a1 b R /\ Par W a2 b R.
Proof.
  pose confluence_size_def n :=
      forall a, size_tm a <= n ->  forall W a1 R, Par W a a1 R -> forall a2, Par W a a2 R -> exists b, Par W a1 b R /\ Par W a2 b R.
  intro n. fold (confluence_size_def n).  eapply (well_founded_induction_type lt_wf).
  clear n. intros n IH. unfold confluence_size_def in *. clear confluence_size_def.
  intros a SZ W a1 R P1 a2 P2.
  inversion P1; inversion P2; subst.
  all: try solve [invert_equality].

  (* 63 subgoals *)
  (* TODO: there may be a way to check the number of subgoals (and guard against a innvalid number) *)

  all: try_Refl_left.
  all: try_Refl_right.
  all: try invert_syntactic_equality.
  all: simpl in SZ; destruct n; try solve [ inversion SZ ].

  - (* two betas *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    destruct (Par_Abs_inversion Par1) as [ax [EQ h0]]; subst;
    destruct (Par_Abs_inversion Par2) as [ay [EQ2 h1]]; subst.
    inversion EQ2. subst.
    exists (open_tm_wrt_tm ay bc).
    split. pick fresh x; eapply open2. auto. eauto. eauto.
    pick fresh x; eapply open2; eauto.
  - (* app beta / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    destruct (Par_Abs_inversion Par1) as [ax [EQ h0]]; subst.
    exists (open_tm_wrt_tm ax bc). inversion Par1; subst.
     + split. pick fresh x; eapply open2. auto. eauto. eauto.
       eapply Par_Beta; eauto.
     + split. pick fresh x; eapply open2. auto. eauto. eauto.
       eapply Par_Beta; eauto.
(*  - (* beta / push *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par1; subst; inversion Par2.
    - (* beta / push combine *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par1; subst; inversion Par2. *)
  - (* app cong / app beta *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    destruct (Par_Abs_inversion Par2) as [ax [EQ h0]]; subst.
    exists (open_tm_wrt_tm ax bc). inversion Par2; subst.
     + split. eapply Par_Beta; eauto.
       pick fresh x; eapply open2. auto. eauto. eauto.
     + split. eapply Par_Beta; eauto. 
       pick fresh x; eapply open2. auto. eauto. eauto.
  - (* app cong / app cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    exists (a_App ac rho R1 bc). split; auto.
(*  - (* app / push *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    inversion Par2; subst.
     + exists (a_Conv (a_App a4 Rel R1 (a_Conv bc R3 g_Triv)) R3 g_Triv).
       split. apply Par_Push; auto. apply Par_Cong. apply Par_App; auto.
       apply Par_Refl. apply Par_erased_tm_fst in Par2. inversion Par2.
       auto.
     + exists (a_Conv (a_App a2 Rel R1 (a_Conv bc R3 g_Triv)) R3 g_Triv).
       split. apply Par_Push; auto. apply Par_Cong. apply Par_App; auto.
     + exists (a_Conv (a_App a2 Rel R1 (a_Conv bc R3 g_Triv)) R3 g_Triv).
       split. econstructor; auto. apply Par_Combine. apply Par_PushCombine.
       auto. econstructor. auto.
  - (* app / push combine *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    pose (P := Par_Cong_inversion Par4).
    inversion P as [b4 Q]. subst.
    inversion Par2; subst.
     + exists (a_Conv (a_App a4 Rel R1 (a_Conv b4 R3 g_Triv)) R3 g_Triv).
       split. apply Par_PushCombine; auto. econstructor.
       econstructor. inversion H1; subst; auto. auto.
     + exists (a_Conv (a_App a2 Rel R1 (a_Conv b4 R3 g_Triv)) R3 g_Triv).
       split. apply Par_PushCombine; auto. econstructor. econstructor; auto.
     + exists (a_Conv (a_App a2 Rel R1 (a_Conv b4 R3 g_Triv)) R3 g_Triv).
       split. apply Par_PushCombine; auto. apply Par_Combine.
       apply Par_PushCombine; auto. *)
  - (* two cbetas *)
    use_size_induction a0 ac Par1 Par2. inversion Par1; subst.
    + exists (open_tm_wrt_co a' g_Triv); split.
      econstructor. eapply Par_erased_tm_snd. eauto.
      inversion Par2; subst. econstructor. eapply Par_erased_tm_snd. eauto.
      pick fresh c. eapply open3 with (c := c) (L := L); eauto.
    + exists (open_tm_wrt_co a'1 g_Triv); split.
      pick fresh c. eapply open3 with (c := c) (L := L); eauto.
      inversion Par2; subst. econstructor. eapply Par_erased_tm_snd. eauto.
      pick fresh c. eapply open3 with (c := c) (L := L); eauto.
  - (* cbeta / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par1; subst.
    + exists (open_tm_wrt_co a' g_Triv). split.
      econstructor. eapply Par_erased_tm_snd. eauto.
      econstructor. eauto.
    + exists (open_tm_wrt_co a'1 g_Triv). split.
      pick fresh c. eapply open3 with (c := c) (L := L); eauto.
      econstructor. eauto.
(*  - (* cbeta / cpush *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par1; subst; inversion Par2. *)
  - (* capp cong / cbeta *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par2; subst.
    + exists (open_tm_wrt_co a'0 g_Triv). split. econstructor. eauto.
      econstructor. eapply Par_erased_tm_snd. eauto.
    + exists (open_tm_wrt_co a'1 g_Triv). split. econstructor. eauto.
      pick fresh c. eapply open3 with (c := c) (L := L); eauto.
  - (* capp cong / capp cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_CApp ac g_Triv). auto.
(*  - (* capp / cpush *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par2; subst.
    + exists (a_Conv (a_CApp a4 g_Triv) R1 g_Triv). split.
      econstructor. auto. econstructor. eapply Par_erased_tm_snd. eauto.
    + exists (a_Conv (a_CApp a2 g_Triv) R1 g_Triv). split.
      econstructor. auto. econstructor. econstructor. eauto.
    + exists (a_Conv (a_CApp a2 g_Triv) R1 g_Triv). split.
      econstructor. auto. eapply Par_Combine. econstructor. eauto. *)
  - (* abs cong / abs cong *)
    pick fresh x.
    use_size_induction_open a0 x ac Par1 Par2.
    exists (a_UAbs rho R1 (close_tm_wrt_tm x ac)).
    split; apply (@Par_Abs_exists x); eauto.
  - (* pi cong / pi cong *)
    pick fresh x.
    use_size_induction A ac Par1 Par2.
    use_size_induction_open B x bc Par3 Par4.
    exists (a_Pi rho ac R1 (close_tm_wrt_tm x bc)).
    split; apply (@Par_Pi_exists x); eauto.
  - (* cabs cong / cabs cong *)
    pick fresh c.
    use_size_induction_open a0 c ac Par1 Par2.
    exists (a_UCAbs (close_tm_wrt_co c ac)).
    split; apply (@Par_CAbs_exists c); eauto.
  - (* cpi cong / cpi cong *)
    use_size_induction A AC Par1 Par2.
    use_size_induction a0 aC Par3 Par4.
    use_size_induction b bC Par5 Par6.
    pick fresh c.
    use_size_induction_open B c BC Par7 Par8.
    exists (a_CPi (Eq aC bC AC R1) (close_tm_wrt_co c BC)).
    split; apply (@Par_CPi_exists c); eauto.
  - (* fam / fam *)
    have E: (Ax a1 A R1 = Ax a2 A0 R3).
    eapply binds_unique; eauto using uniq_toplevel.
    inversion E. subst.
    exists a2. split; econstructor; eapply Par_erased_tm_snd; eauto.
(*  - (* cong / cong *)
   use_size_induction a0 ac Par1 Par2.
   exists (a_Conv ac R0 g_Triv). split; constructor; auto.
  - (* cong / combine *)
   use_size_induction a0 ac Par1 Par2.
   inversion Par2; exists ac; subst; split; eauto.
  - (* combine / cong *)
   use_size_induction a0 ac Par1 Par2.
   inversion Par1; exists ac; subst; split; eauto.
  - (* combine / combine *)
   use_size_induction a0 ac Par1 Par2. exists ac. split; eauto.
  - (* push / beta *)
   use_size_induction a0 ac Par1 Par2.
   inversion Par2; subst. inversion Par1.
   inversion Par1.
  - (* push / app *)
   use_size_induction a0 ac Par1 Par2.
   use_size_induction b1 bc Par3 Par4.
   inversion Par1; subst.
     + exists (a_Conv (a_App a3 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
       split. apply Par_Cong. apply Par_App; auto. econstructor.
       inversion H1. auto. apply Par_Push; auto.
     + exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
       split. apply Par_Cong. apply Par_App; auto. apply Par_Push; auto.
     + exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
       split. apply Par_Combine. apply Par_PushCombine. auto. econstructor.
       auto. econstructor; auto.
  - (* push / push *)
   use_size_induction a0 ac Par1 Par2.
   use_size_induction b1 bc Par3 Par4.
   inversion Par1; subst.
     + inversion Par2; subst.
        * exists (a_Conv (a_App a3 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          inversion H1; subst.
          split; econstructor; econstructor; econstructor; eauto.
        * exists (a_Conv (a_App a3 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          inversion H1; subst.
          split. econstructor; econstructor; econstructor; eauto.
          econstructor; econstructor; eauto.
        * exists (a_Conv (a_App a3 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          split. econstructor; econstructor. inversion H1; subst; auto.
          econstructor. auto. apply Par_Combine. apply Par_PushCombine.
          auto. econstructor. auto.
     + inversion Par2; subst.
        * exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          inversion H9; subst.
          split. econstructor; econstructor; eauto.
          econstructor; econstructor; econstructor; eauto.
        * exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          split; econstructor; econstructor; eauto.
        * exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          split. econstructor; econstructor; eauto. apply Par_Combine.
          apply Par_PushCombine. auto. econstructor. auto.
      + inversion Par2; subst.
        * exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          split. apply Par_Combine. apply Par_PushCombine.
          auto. econstructor. auto. econstructor; econstructor.
          inversion H9; subst; auto. econstructor. auto.
        * exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          split.  apply Par_Combine. apply Par_PushCombine. auto.
          econstructor. auto. econstructor; econstructor; eauto.
        * exists (a_Conv (a_App a2 Rel R2 (a_Conv bc R0 g_Triv)) R0 g_Triv).
          split; apply Par_Combine; apply Par_PushCombine; eauto.
  - (* push / push combine *)
   use_size_induction a0 ac Par1 Par2.
   use_size_induction b1 bc Par3 Par4.
   pose (P := Par_Cong_inversion Par4).
   inversion P as [b4 Q]. subst.
   inversion Par1; subst.
    + inversion Par2; subst.
       * exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H1; subst. split; econstructor; econstructor.
         econstructor; auto. apply Par_Combine; auto. econstructor; auto. auto.
       * exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H1; subst. split; econstructor; econstructor.
         econstructor; auto. apply Par_Combine; auto. auto. auto.
       * exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H1; subst. split. econstructor; econstructor.
         econstructor; auto. apply Par_Combine; auto. apply Par_Combine.
         apply Par_PushCombine; auto.
     + inversion Par2; subst.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H9; subst. split; econstructor; econstructor. auto.
         apply Par_Combine; auto. econstructor; auto. auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split. econstructor; econstructor; auto.
         apply Par_Combine. apply Par_PushCombine; auto.
     + inversion Par2; subst.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H9; subst. split. apply Par_Combine.
         apply Par_PushCombine; auto. econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split. apply Par_Combine.
         apply Par_PushCombine; auto. econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split; apply Par_Combine; apply Par_PushCombine; auto.
  - (* push combine / beta *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par2; subst; inversion Par1.
  - (* push combine / app *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 bc Par3 Par4.
    pose (P := Par_Cong_inversion Par3).
    inversion P as [b4 Q]. subst.
    inversion Par1; subst.
     + exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
       split. econstructor; econstructor. econstructor.
       inversion H1; subst; auto. auto. apply Par_PushCombine; auto.
     + exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
       split. econstructor; econstructor; auto.
       apply Par_PushCombine; auto.
     + exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
       split. apply Par_Combine. apply Par_PushCombine; auto.
       apply Par_PushCombine; auto.
  - (* push combine / push *)
   use_size_induction a0 ac Par1 Par2.
   use_size_induction b1 bc Par3 Par4.
   pose (P := Par_Cong_inversion Par3).
   inversion P as [b4 Q]. subst.
   inversion Par2; subst.
    + inversion Par1; subst.
       * exists (a_Conv (a_App a5 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         inversion H1; subst. split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a5 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         inversion H1; subst. split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a5 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         inversion H1; subst. split. apply Par_Combine.
         apply Par_PushCombine; auto. econstructor; econstructor.
         econstructor; auto. apply Par_Combine; auto. 
     + inversion Par1; subst.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         inversion H9; subst. split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         split. apply Par_Combine. apply Par_PushCombine; auto.
         econstructor; econstructor; auto.
     + inversion Par1; subst.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         inversion H9; subst. split. econstructor; econstructor; auto.
         apply Par_Combine. apply Par_PushCombine; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         split. econstructor; econstructor; auto. apply Par_Combine.
         apply Par_PushCombine; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R4 g_Triv)) R4 g_Triv).
         split; apply Par_Combine; apply Par_PushCombine; auto.
  - (* push combine / push combine *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 bc Par3 Par4.
    pose (P := Par_Cong_inversion Par3).
    inversion P as [b4 Q]. subst.
    inversion Par1; subst.
    + inversion Par2; subst.
       * exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H1; subst. split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H1; subst. split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a3 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H1; subst. split. econstructor; econstructor.
         econstructor; auto. auto. apply Par_Combine; auto.
     + inversion Par2; subst.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H9; subst. split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split; econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split. econstructor; econstructor; auto.
         apply Par_Combine. apply Par_PushCombine; auto.
     + inversion Par2; subst.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         inversion H9; subst. split. apply Par_Combine.
         apply Par_PushCombine; auto. econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split. apply Par_Combine.
         apply Par_PushCombine; auto. econstructor; econstructor; auto.
       * exists (a_Conv (a_App a2 Rel R2 (a_Conv b4 R0 g_Triv)) R0 g_Triv).
         split; apply Par_Combine; apply Par_PushCombine; auto.
  - (* cpush / cbeta *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par2; subst; inversion Par1.
  - (* cpush / capp *) 
    use_size_induction a0 ac Par1 Par2.
    inversion Par1; subst.
    + exists (a_Conv (a_CApp a3 g_Triv) R0 g_Triv). split.
      econstructor. eapply Par_erased_tm_snd. eauto. econstructor. auto.
    + exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv). split.
      econstructor. econstructor. eauto. econstructor. auto.
    + exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv). split.
      eapply Par_Combine. econstructor. eauto. econstructor. auto.
   - (* cpush / cpush *)
    use_size_induction a0 ac Par1 Par2.
    inversion Par1; subst.
     + inversion Par2; subst.
        * exists (a_Conv (a_CApp a3 g_Triv) R0 g_Triv).
          split; econstructor; eapply Par_erased_tm_snd; eauto.
        * exists (a_Conv (a_CApp a3 g_Triv) R0 g_Triv).
          split. econstructor; eapply Par_erased_tm_snd; eauto.
          econstructor; eauto.
        * exists (a_Conv (a_CApp a3 g_Triv) R0 g_Triv).
          split. econstructor; eapply Par_erased_tm_snd; eauto.
          apply Par_Combine. econstructor; eauto.
     + inversion Par2; subst.
        * exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv).
          split. econstructor; eauto.
          econstructor; eapply Par_erased_tm_snd; eauto.
        * exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv).
          split; econstructor; eauto.
        * exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv).
          split. econstructor; eauto.
          apply Par_Combine. econstructor; eauto.
      + inversion Par2; subst.
        * exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv).
          split. apply Par_Combine. econstructor; eauto. 
          econstructor; eapply Par_erased_tm_snd; eauto.
        * exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv).
          split. apply Par_Combine. econstructor; eauto. econstructor; eauto.
        * exists (a_Conv (a_CApp a2 g_Triv) R0 g_Triv).
          split; apply Par_Combine; econstructor; eauto. *)
Qed.

Lemma confluence : forall W a a1 R, Par W a a1 R -> 
                   forall a2, Par W a a2 R -> exists b,
                           Par W a1 b R /\ Par W a2 b R.
Proof.
  intros.
  eapply confluence_size; eauto.
Qed.


(* ---------------------------------------------------------------------- *)

Lemma multipar_lc1 : forall W a b R, multipar W a b R -> lc_tm a.
Proof. intros. eapply erased_lc; eapply multipar_erased_tm_fst; eauto.
Qed.

Lemma multipar_lc2 : forall W a b R, multipar W a b R -> lc_tm b.
Proof. intros. eapply erased_lc; eapply multipar_erased_tm_snd; eauto.
Qed.

Lemma multipar_Star : forall W A B R, multipar W A B R -> A = a_Star -> B = a_Star.
Proof.
  intros W A B R H. induction H. auto.
  inversion H; intro K; auto; try inversion K.
Qed.


Lemma multipar_Bullet : forall W B R, multipar W a_Bullet B R -> B = a_Bullet.
Proof.
  intros W B R H. dependent induction H. auto.
  inversion H; auto; try inversion K.
Qed.

(*
Lemma Par_Const : forall W T b R,
    Par W (a_Const T) b R -> b = a_Const T.
Proof.
  intros. dependent induction H; eauto.
Qed.

Lemma multipar_Const : forall W T b R,
    multipar W (a_Const T) b R ->
    (b = a_Const T).
Proof.
  intros W T b R H. dependent induction H; eauto using Par_Const.
Qed.
*)

Lemma multipar_Pi : forall W rho A B R', multipar W A B R' -> 
      forall A1 R A2, A = a_Pi rho A1 R A2 -> exists B1 B2, B = (a_Pi rho B1 R B2).
Proof.
intros W rho A B R' H. induction H. intros. subst. exists A1, A2. auto.
intros. subst.
inversion H; subst; destruct (IHmultipar _ _ _ eq_refl) as [B1 [B2 EQ]]; auto;
exists B1, B2; auto.
Qed.

Lemma multipar_CPi : forall W A C R', multipar W A C R' -> 
        forall A1 A2 A3 R B, A = a_CPi (Eq A1 A2 A3 R) B -> exists B1 B2 B3 C2,
        C = (a_CPi (Eq B1 B2 B3 R) C2).
Proof.
  intros W A C R' H. induction H; intros; subst.
  exists A1, A2, A3, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ _ _ _ eq_refl) as [B1 [B2 [C2 EQ]]];
    auto; exists B1, B2, C2; auto.
Qed.

Lemma multipar_UAbs : forall W rho R a b R',
    multipar W (a_UAbs rho R a) b R' ->
    (exists b2, b = (a_UAbs rho R b2)).
Proof.
  intros W rho R a b R' H. dependent induction H.
  - exists a. auto.
  - destruct (Par_Abs_inversion H) as [a' [EQ _]]; subst.
    destruct (IHmultipar _ _ a' eq_refl) as [b2 EQ2]; subst; clear IHmultipar.
    exists b2. auto.
Qed.

Lemma multipar_CAbs : forall W A C R', multipar W A C R' -> 
        forall A1 A2 A3 R B, A = a_CAbs (Eq A1 A2 A3 R) B -> exists B1 B2 B3 C2,
        C = (a_CAbs (Eq B1 B2 B3 R) C2).
Proof.
  intros W A C R' H. induction H; intros; subst.
  exists A1, A2, A3, B. auto.
  inversion H; subst; destruct (IHmultipar _ _ _ _ _ eq_refl) as [B1 [B2 [C2 EQ]]];
    auto; exists B1, B2, C2; auto.
Qed.

Lemma consist_sym : forall a b R, consistent a b R -> consistent b a R.
Proof. intros. induction H; eauto.
Qed.

(* ----------------------------------------------------------------- *)

(* Properties of Path *)

Lemma Path_lc : forall F a R, Path F a R -> lc_tm a.
Proof. intros. induction H; eauto.
Qed.

Lemma uniq_Path : forall F F' a R, Path F a R -> Path F' a R -> F = F'.
Proof. intros. generalize dependent F'. induction H; intros; auto.
       inversion H1; subst. auto. inversion H1; subst. eauto.
       inversion H0; subst. eauto. 
Qed.

Lemma decide_Path : forall W a R, erased_tm W a R -> (exists F, Path F a R) \/
                                     (forall F, not (Path F a R)).
Proof.
  induction a; intros R' E.
  all: try solve [right; move => F h1; inversion h1].
  - inversion E; subst. apply IHa1 in H5. destruct H5 as [[F h0]|n].
    left. exists F. econstructor; auto. eapply erased_lc; eauto.
    right. intros. intro. inversion H; subst. pose (Q := n F). contradiction.
  - inversion E; subst. destruct (sub_dec R R') as [P1 | P2].
    right. intros. intro. inversion H; subst. have Q: (Ax a A R = Ax a0 A0 R1).
    eapply binds_unique; eauto using uniq_toplevel.
    inversion Q. subst. contradiction. left. exists F. eauto.
  - inversion E; subst. apply IHa in H3. destruct H3 as [[F h0]|n].
    left. exists F. eauto. right. intros. intro. inversion H; subst.
    pose (Q := n F). contradiction.
Qed.

Lemma Par_Path : forall F a R W a', Path F a R -> Par W a a' R -> Path F a' R.
Proof. intros. generalize dependent a'. induction H; intros.
       - inversion H1; subst. eauto. have E: (Ax a A R1 = Ax a' A0 R2).
         eapply binds_unique; eauto using uniq_toplevel.
         inversion E. subst. contradiction.
       - inversion H1; subst. eauto. apply IHPath in H9.
         inversion H9. apply IHPath in H9. econstructor; auto.
         apply Par_erased_tm_snd in H10. eapply erased_lc; eauto.
       - inversion H0; subst. eauto. apply IHPath in H3. inversion H3.
         apply IHPath in H3. econstructor; auto.
Qed.

Lemma multipar_Path :  forall F a R W a', Path F a R -> multipar W a a' R ->
                       Path F a' R.
Proof. intros. induction H0; auto. apply IHmultipar. eapply Par_Path; eauto.
Qed.

Lemma multipar_Path_join_head : forall F1 F2 W a1 a2 c R,
      multipar W a1 c R -> multipar W a2 c R ->
      Path F1 a1 R -> Path F2 a2 R -> F1 = F2.
Proof. intros. eapply multipar_Path in H; eauto.
       eapply multipar_Path in H0; eauto. eapply uniq_Path; eauto.
Qed.

(* Paths and consistency *)

Inductive Path_head_form : tm -> Prop :=
   | head_Fam : forall F, Path_head_form (a_Fam F)
   | head_App : forall a rho R b, Path_head_form (a_App a rho R b)
   | head_CApp : forall a g, Path_head_form (a_CApp a g).
(*    | head_Conv : forall a R g, Path_head_form (a_Conv a R g). *)
Hint Constructors Path_head_form.

Inductive not_Path_head_form : tm -> Prop :=
   | not_head_Pi : forall rho A R b, not_Path_head_form (a_Pi rho A R b)
   | not_head_CPi : forall phi b, not_Path_head_form (a_CPi phi b).
Hint Constructors not_Path_head_form.

Lemma Path_head_form_Path_consist : forall W F a b R, Path F a R ->
                       multipar W a b R -> consistent a b R.
Proof. intros. eapply consistent_a_Path; eauto. eapply multipar_Path; eauto.
Qed.

Lemma Path_head_form_no_Path_consist : forall a b R, Path_head_form a ->
         lc_tm b -> (forall F, ~(Path F a R)) -> consistent a b R.
Proof. intros. eapply consistent_a_Step_L. auto.
       intro H2; inversion H2; subst; try (inversion H; fail).
       pose (Q := H1 F); contradiction.
Qed.

Lemma Path_head_form_consist : forall W a b R, Path_head_form a ->
                multipar W a b R -> consistent a b R.
Proof. intros. inversion H; subst.
       all: (assert (H' := H0); apply multipar_erased_tm_fst in H';
       apply decide_Path in H'; inversion H' as [[F0 Q]|n]).
       all: try(eapply Path_head_form_Path_consist; eauto; fail).
       all: try(apply multipar_lc2 in H0;
            eapply Path_head_form_no_Path_consist; eauto; fail).
Qed.

Lemma Path_head_form_join_consist : forall W a b R, joins W a b R ->
             Path_head_form a -> Path_head_form b -> consistent a b R.
Proof. intros. destruct H as (t & MSL & MSR).
       assert (P := MSL); assert (Q := MSR).
       apply multipar_erased_tm_fst in P. apply multipar_erased_tm_fst in Q.
       apply decide_Path in P. apply decide_Path in Q.
       inversion P as [[F1 S]|n]. inversion Q as [[F2 S']|n'].
       assert (F1 = F2). eapply multipar_Path_join_head. eapply MSL.
       eapply MSR. auto. auto. subst. eauto.
       apply multipar_lc1 in MSL. apply consist_sym.
       eapply Path_head_form_no_Path_consist; eauto.
       apply multipar_lc1 in MSR. eapply Path_head_form_no_Path_consist; eauto.
Qed.


Lemma Path_head_not_head_join_consist : forall W a b R, joins W a b R ->
             Path_head_form a -> not_Path_head_form b -> consistent a b R.
Proof. intros. destruct H as (t & MSL & MSR).
    assert (P := MSL). apply multipar_erased_tm_fst in P.
    apply decide_Path in P. inversion P as [[F S]|n].
    eapply multipar_Path in MSL; eauto. inversion H1; subst.
    destruct (multipar_Pi MSR eq_refl) as (b1 & b2 & Q); subst.
    inversion MSL. destruct phi; subst.
    destruct (multipar_CPi MSR eq_refl) as (b1 & b2 & B & C & Q). subst.
    inversion MSL. apply multipar_lc1 in MSR.
    apply Path_head_form_no_Path_consist; eauto.
Qed.

Lemma Path_not_head_head_join_consist : forall W a b R, joins W a b R ->
             not_Path_head_form a -> Path_head_form b -> consistent a b R.
Proof. intros. destruct H as (t & MSL & MSR).
    assert (Q := MSR). apply multipar_erased_tm_fst in Q.
    apply decide_Path in Q. inversion Q as [[F S]|n].
    eapply multipar_Path in MSR; eauto. inversion H0; subst.
    destruct (multipar_Pi MSL eq_refl) as (b1 & b2 & U); subst.
    inversion MSR. destruct phi; subst.
    destruct (multipar_CPi MSL eq_refl) as (b' & b2 & B & C & U). subst.
    inversion MSR. apply multipar_lc1 in MSL.
    apply consist_sym. apply Path_head_form_no_Path_consist; eauto.
Qed.

(* --------------------------------------------------- *)

Lemma joins_lc_fst : forall W a b R, joins W a b R -> lc_tm a.
Proof. intros. inversion H as [T [H1 H2]]. 
       apply multipar_erased_tm_fst in H1.
       eapply erased_lc. eauto.
Qed.

Lemma joins_lc_snd : forall W a b R, joins W a b R -> lc_tm b.
Proof. intros. inversion H as [T [H1 H2]].
       apply multipar_erased_tm_fst in H2.
       eapply erased_lc. eauto.
Qed.

(* Proof that joinability implies consistency. *)

Ltac step_left := eapply consistent_a_Step_R; [eapply joins_lc_fst; eauto |intro N; inversion N; subst; inversion H]; fail.
Ltac step_right := eapply consistent_a_Step_L; [eapply joins_lc_snd; eauto | intro N; inversion N; subst; inversion H]; fail.

(* look for a multipar involving a head form and apply the appropriate lemma for that
   head form. Note: for paths, the lemma has already been applied so we only need
   to look for a hypothesis about path consistency. *)
Ltac multipar_step :=
  match goal with
  | [ SIDE : multipar _ a_Star _ _ |- _ ] =>
    apply multipar_Star in SIDE; auto; subst
  (* *)
  | [ SIDE : multipar _ (a_Pi _ _ _ _) _ _ |- _ ] =>
    destruct (multipar_Pi SIDE eq_refl) as [b1' [b2' EQ]]; clear SIDE; subst
  | [ SIDE : multipar _ (a_CPi ?phi _) _ _ |- _ ] =>
    try (destruct phi); destruct (multipar_CPi SIDE eq_refl)
      as (B1' & B2' & C1' & C2' &  EQ); clear SIDE; subst
(*  | [ SIDE : multipar _ (a_Const ?T) _ _ |- _ ] =>
    apply multipar_Const in SIDE; auto; rename SIDE into EQ *)
  end.

Lemma join_consistent : forall W a b R, joins W a b R -> consistent a b R.
Proof.
  intros. assert (H' := H).
  destruct H as (TT & MSL & MSR).
  destruct a; try step_right; destruct b; try step_left; auto.
  all: try multipar_step; try (multipar_step; inversion EQ).
  all: try (apply consist_sym; eapply Path_head_form_consist; eauto; fail).
  all: try (eapply Path_head_form_consist; eauto; fail).
  all: try (eapply Path_head_form_join_consist; eauto; fail).
  all: try (eapply Path_head_not_head_join_consist; eauto; fail).
  all: try (eapply Path_not_head_head_join_consist; eauto; fail).
  - destruct (multipar_Pi MSL eq_refl) as [c1 [c2 EQ]].
    inversion EQ; subst. econstructor. apply joins_lc_fst in H'.
    inversion H'; auto. eapply joins_lc_fst; eauto. apply joins_lc_snd in H'.
    inversion H'; auto. eapply joins_lc_snd; eauto.
  - destruct phi. destruct (multipar_CPi MSL eq_refl)
    as (c1 & c2 & c3 & c4 &  EQ). inversion EQ; subst. econstructor.
    apply joins_lc_fst in H'. inversion H'; auto. 
    eapply joins_lc_fst; eauto. apply joins_lc_snd in H'.
    inversion H'; auto. eapply joins_lc_snd; eauto.
Qed.

(*

a  -> b -->* c      d - by confluence
|     |      |      e - by induction
v     v      v
a2 -> d -->* e
*)

Lemma multipar_confluence_helper : forall W a a1 R, multipar W a a1 R
-> forall a2, Par W a a2 R -> exists e, Par W a1 e R /\ multipar W a2 e R.
Proof.
  intros W a a1 R H. induction H.
  - intros. exists a2. split. auto. econstructor.
    eapply Par_erased_tm_snd; eauto.
  - intros. destruct (confluence H H1) as [d [Hx Hy]].
      destruct (IHmultipar d Hx) as [e [LL RR]]; auto.
      exists e. split; eauto.
Qed.

(*

a -->  b -->* c    d - by prior lemma
|      |      |    e - by induction.
v      v      v
*      *      *
a2 --> d -->* e

*)

Lemma multipar_confluence : forall W a a1 R, multipar W a a1 R
-> forall a2, multipar W a a2 R ->
   exists b, multipar W a1 b R /\ multipar W a2 b R.
Proof.
  intros W a a1 R MP. induction MP; intros.
 - exists a2. split. eauto. econstructor.
   eapply multipar_erased_tm_snd; eauto.
 - destruct (multipar_confluence_helper H0 H) as [d [Hx Hy]].
   destruct (IHMP d Hy) as [e [LL RR]]; auto.
   exists e. split; eauto.
Qed.

Lemma multipar_append : forall W a b c R, multipar W a b R -> 
                        multipar W b c R -> multipar W a c R.
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


Lemma join_transitive : forall W a b R, joins W a b R -> 
                        forall c, joins W b c R -> joins W a c R.
Proof.
  intros W a b R H. destruct H as [t [H1 H2]].
  intros c H. destruct H as [t' [H3 H4]].
  destruct (multipar_confluence H2 H3) as [d [H5 H6]].
  unfold joins.
  exists d. split; eapply multipar_append; eauto.
Qed.

Lemma join_symmetry: forall W a b R, joins W a b R -> joins W b a R.
Proof.
  intros W a b R H.
  destruct H as [ac h0].
  split_hyp.
  exists ac; eauto.
Qed.


Definition extends (G G2 : context) := exists G1, G = G1 ++ G2.

Lemma Good_NoAssn: forall c phi G D, Good G D -> c `notin` D -> Good ((c, Co phi) :: G) D.
Proof.
  intros.
  unfold Good in *. intros.
  apply binds_cons_iff in H1.
  inversion H1. inversion H3; subst. contradiction.
  eapply H; eauto.
Qed.

Hint Resolve Good_NoAssn.

Lemma Good_add_tm: forall G D x A R, Good G D -> x `notin` (dom G) ->
                                     Good ((x, Tm A R)::G ) D.
Proof.
  intros.
  unfold Good in *.
  intros. apply binds_cons_iff in H1.
  inversion H1 as [P1 | P2]. inversion P1. inversion H4.
  destruct (H c1 A0 B1 T1 R0 P2 H2) as (t & Eq). simpl.
  replace ((x, R) :: (ctx_to_rctx G)) with (nil ++ [(x, R)] ++ (ctx_to_rctx G)); auto.
  inversion Eq. pose (Q := Par_rctx_uniq H3). apply notin_ctx_rctx in H0.
  exists t; split; eapply par_app_rctx; simpl_env; eauto.
Qed.

Lemma Good_add_tm_2: forall G D x A R, x `notin` dom G -> Good G D -> Good ((x, Tm A R)::G ) (add x D).
Proof.
  intros G D x A R N H0.
  unfold Good in *. intros.
  apply binds_cons_1 in H.
  destruct H. destruct H. inversion H2.
  destruct (H0 c1 A0 B1 T1 R0 H) as [C [H2 H3]].
  move: (binds_In _ c1 _ _ H) => b0. fsetdec. simpl.
  replace ((x, R) :: (ctx_to_rctx G)) with (nil ++ [(x, R)] ++ (ctx_to_rctx G)); auto.
  pose (Q := Par_rctx_uniq H3). apply notin_ctx_rctx in N.
  exists C; split; eapply par_app_rctx; simpl_env; eauto.
Qed.


Lemma multipar_app_left:
  forall rho R R' a a' c' W, erased_tm W a R -> multipar W a' c' R' ->
                      multipar W (a_App a rho R' a') (a_App a rho R' c') R.
Proof.
  induction 2; eauto; try done.
Qed.

Lemma multipar_capp_left: forall a a' W R, multipar W a a' R ->
                     multipar W (a_CApp a g_Triv) (a_CApp a' g_Triv) R.
Proof.
  induction 1; eauto; try done.
Qed.

Lemma join_capp: forall a a' W R, joins W a a' R ->
                     joins W (a_CApp a g_Triv) (a_CApp a' g_Triv) R.
Proof.
  unfold joins.
  intros a a' W R H.
  destruct H as [ac h0].
  split_hyp.
  exists (a_CApp ac g_Triv).
  repeat split; eauto.
  apply multipar_capp_left; auto.
  apply multipar_capp_left; auto.
Qed.

Lemma multipar_app_lr: forall rho R R' a a' c c' W,
                       multipar W a c R -> multipar W  a' c' R' ->
                       multipar W (a_App a rho R' a') (a_App c rho R' c') R.
Proof. intros. induction H.
  eapply multipar_app_left; auto.
  apply (@mp_step W _ _ (a_App b rho R' a')); eauto.
  econstructor. auto. econstructor. eapply multipar_erased_tm_fst; eauto.
Qed.

Lemma join_app: forall rho R R' a a' b b' W, joins W a b R ->
                       joins W a' b' R' ->
                       joins W (a_App a rho R' a') (a_App b rho R' b') R.
Proof.
  unfold joins.
  intros rho R R' a a' b b' W H H0.
  destruct H as [ac h0].
  destruct H0 as [ac' h1].
  split_hyp.
  exists (a_App ac rho R' ac').
  repeat split; eauto.
  apply multipar_app_lr; auto; try solve [eapply erased_lc; eauto].
  apply multipar_app_lr; auto; try solve [eapply erased_lc; eauto].
Qed.


Lemma multipar_UAbs_exists :  ∀ (x : atom) W(rho : relflag) R R' (a a' : tm),
    x `notin` fv_tm_tm_tm a
       → multipar ([(x,R)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) a' R'
       → multipar W (a_UAbs rho R a) (a_UAbs rho R (close_tm_wrt_tm x a')) R'.
Proof.
  intros.
  dependent induction H0.
  autorewrite with lngen. econstructor.
  apply (erased_a_Abs (union (singleton x) (dom W))); eauto.
  intros x0 h0.
  rewrite (tm_subst_tm_tm_intro x a (a_Var_f x0)); auto.
  replace ([(x0,R)] ++ W) with (nil ++ [(x0,R)] ++ W); auto.
  assert (uniq ([(x,R)] ++ W)). {eapply rctx_uniq; eauto. }
  eapply subst_tm_erased. simpl_env. eapply erased_app_rctx; eauto.
  econstructor; eauto. solve_uniq.
  eapply mp_step.
  eapply Par_Abs_exists with (x:=x); eauto.
  eapply IHmultipar; eauto. autorewrite with lngen. auto.
  autorewrite with lngen. auto.
Qed.

Lemma multipar_iapp : forall W a c y L R R',
    y `notin` fv_tm_tm_tm a \u L ->
    (forall x, x `notin` L -> RhoCheck Irrel x (open_tm_wrt_tm a (a_Var_f x))) ->
    multipar ([(y,R)] ++ W) (open_tm_wrt_tm a a_Bullet) c R' ->
    multipar W (a_UAbs Irrel R a) (a_UAbs Irrel R (close_tm_wrt_tm y c)) R'.
Proof.
  intros.
  eapply multipar_UAbs_exists; auto.
  move: (H0 y ltac:(auto)) => h0.
  inversion h0.
  rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm a (a_Var_f y)) a_Bullet y); eauto.
  rewrite - tm_subst_tm_tm_intro; eauto.
Qed.

Lemma joins_iapp : forall W a1 a2 L1 L2 R R',
    (forall x, x `notin` L1 -> RhoCheck Irrel x (open_tm_wrt_tm a1 (a_Var_f x))) ->
    (forall x, x `notin` L2 -> RhoCheck Irrel x (open_tm_wrt_tm a2 (a_Var_f x))) ->
    joins W (open_tm_wrt_tm a1 a_Bullet) (open_tm_wrt_tm a2 a_Bullet) R' ->
    joins W (a_UAbs Irrel R a1) (a_UAbs Irrel R a2) R'.
Proof.
  intros.
  destruct H1 as (T & P1 & P2).
  unfold joins.
  pick fresh y.
  exists (a_UAbs Irrel R (close_tm_wrt_tm y T)).
  assert (uniq W). { eapply rctx_uniq. eapply multipar_erased_tm_fst; eauto. }
  repeat split; eauto.
  eapply multipar_iapp with L1; auto.
  replace ([(y,R)] ++ W) with (nil ++ [(y,R)] ++ W); auto.
  apply multipar_app_rctx; auto.
  eapply multipar_iapp with L2; auto.
  replace ([(y,R)] ++ W) with (nil ++ [(y,R)] ++ W); auto.
  apply multipar_app_rctx; auto.
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

Lemma consistent_mutual:
  (forall S a A R,   Typing S a A R -> True) /\
  (forall S phi,   PropWff S phi -> True) /\
  (forall S D p1 p2, Iso S D p1 p2 -> Good S D -> (forall A1 B1 T1 A2 B2 T2 R1 R2,
                     p1 = Eq A1 B1 T1 R1 -> p2 = Eq A2 B2 T2 R2 ->
    (R1 = R2 /\ joins (ctx_to_rctx S) A1 A2 R1 /\ joins (ctx_to_rctx S) B1 B2 R1 /\ 
     joins (ctx_to_rctx S) T1 T2 R1))) /\
  (forall S D A B T R,   DefEq S D A B T R -> Good S D -> joins(ctx_to_rctx S) A B R) /\
  (forall S,       Ctx S -> True).
Proof.
  apply typing_wff_iso_defeq_mutual; eauto; try done.
  - intros.
    inversion H2; subst.
    inversion H3; subst.
    repeat split; eauto. unfold joins.
    exists T2; eauto. apply DefEq_regularity in d0. inversion d0; subst.
    split; econstructor; eapply Typing_erased; eauto.
  - intros. inversion H3; subst.
    inversion H4; subst.
    eapply typing_erased_mutual in p; eauto; inversion p as [px [py pz]].
    repeat split; eauto.
    all: unfold joins.
    exists A3; split; econstructor; eauto.
    exists B2; split; econstructor; eauto.
  - intros. destruct (H H0) as [T [P1 P2]]. 
    inversion H1. inversion H2.
    subst.
    destruct (multipar_CPi P1 eq_refl) as [Ax [Bx [Tx [By EQ]]]].
    subst. 
    pose K1 := multipar_CPi_phi_proj P1.
    pose K2 := multipar_CPi_phi_proj P2.
    split_hyp. subst.
    repeat split; unfold joins.
    exists Ax; split; auto.
    exists Bx; split; auto.
    exists Tx; split; auto.
  - intros. edestruct H0; eauto. inversion H1.
    exists x; split; apply par_multipar; auto.
  - (* refl *)
    intros.
    unfold joins. exists a; split; econstructor; eapply Typing_erased; eauto.
  - (* symmetry *)
    intros.
    unfold joins in *. destruct H as [c [L R0]]; auto.
    exists c. tauto.
  - (* transitivity *)
    intros. eapply join_transitive; eauto.
  - (* sub *)
    intros. unfold joins in *. destruct H as [c [L R0]]; auto.
    exists c; split; eapply multipar_sub; eauto.
  - (* confluence *)
    intros.
    unfold joins in *.
    have p: Par (ctx_to_rctx G) a1 a2 R.
    { inversion b; subst; apply Typing_erased in t; inversion t; subst.
      econstructor; econstructor; eauto. econstructor; econstructor; eauto.
      econstructor; eauto.
      }
    exists a2; split; econstructor; eauto.
    econstructor. all: eapply Par_erased_tm_snd; eauto.
  - (* pi-cong *)
    intros. destruct (H H4) as [Ax [P1 P2]].
    pick fresh x.
    destruct (H0 x ltac:(auto) (Good_add_tm H4 ltac:(auto))) as [Bx [Q1 Q2]].
    unfold joins. exists (a_Pi rho Ax R (close_tm_wrt_tm x Bx)); split;
    apply multipar_Pi_exists; eauto.
  - (* abs-cong *)
    intros. pick fresh x.
    destruct (H x ltac:(auto) (Good_add_tm H1 ltac:(auto))) as [b [Q1 Q2]].
    unfold joins. exists (a_UAbs rho R (close_tm_wrt_tm x b)); split;
    apply multipar_Abs_exists; eauto.
  - intros.
    apply join_app; auto.
  - intros. destruct (H H1) as [T [P1 P2]].
    apply multipar_erased_tm_fst in P1. apply rctx_uniq in P1.
    apply join_app; auto.
    exists a_Bullet. repeat split; econstructor; econstructor; auto.
  - intros. destruct (H H0) as [T [P1 P2]].
    destruct (multipar_Pi P1 eq_refl) as [Ax [Bx P]]. subst.
    apply multipar_Pi_A_proj in P1.
    apply multipar_Pi_A_proj in P2.
    exists Ax; auto.
  - intros. destruct (H H1) as [T [P1 P2]].
    destruct (multipar_Pi P1 eq_refl) as [Ax [Bx P]]. subst.
    apply (multipar_Pi_B_proj) in P1.
    apply (multipar_Pi_B_proj) in P2.
    inversion P1 as [L1 Q1]. inversion P2 as [L2 Q2].
    destruct (H0 H1) as [ax [P3 P4]].
    pick fresh x.
    rewrite (tm_subst_tm_tm_intro x); auto.
    rewrite (tm_subst_tm_tm_intro x B2); auto.
    replace (ctx_to_rctx G) with (nil ++ (ctx_to_rctx G)); auto.
    exists (tm_subst_tm_tm ax x (open_tm_wrt_tm Bx (a_Var_f x))); split;
    eapply multipar_subst3; simpl_env; eauto.
  - (* cpi-cong *)
    intros. destruct (H H4 a1 b1 A1 a2 b2 A2 R R eq_refl eq_refl) as [_ [J1 [J2 J3]]].
    inversion J1 as [ax [P1 P2]]. inversion J2 as [bx [P3 P4]].
    inversion J3 as [Ax [P5 P6]].
    pick fresh c. destruct (H0 c ltac:(auto)) as [Bx [P7 P8]].
    apply Good_NoAssn; auto.
    exists (a_CPi (Eq ax bx Ax R) (close_tm_wrt_co c Bx)); split;
    apply multipar_CPi_exists; auto.
  - intros. pick fresh c.
    destruct (H c ltac:(auto) (Good_NoAssn H1 ltac:(auto))) as [t [P1 P2]].
    exists (a_UCAbs (close_tm_wrt_co c t)); split;
    apply multipar_CAbs_exists; auto.
  - intros.
    apply join_capp; auto.
  - intros. destruct (H H2) as [t [P1 P2]].
    destruct (multipar_CPi P1 eq_refl) as (c1 & c2 & C & E & P).
    subst. apply multipar_CPi_B_proj in P1. apply multipar_CPi_B_proj in P2.
    inversion P1 as [L1 Q1]. inversion P2 as [L2 Q2].
    pick fresh c.
    rewrite (co_subst_co_tm_intro c); auto.
    rewrite (co_subst_co_tm_intro c B2); auto.
    exists (co_subst_co_tm g_Triv c (open_tm_wrt_co E (g_Var_f c))); split;
    apply multipar_subst4; auto.
  - intros. destruct (H0 H1 a b A a' b' A' R R' eq_refl eq_refl) as (EQ & P1 & P2 & P3).
    subst.
    apply join_transitive with (b := a); eauto.
    apply join_symmetry; auto.
    apply join_transitive with (b := b); eauto.
(*  - intros. destruct (H H1) as [t [P1 P2]].
    exists t; split; eapply multipar_sub; eauto. *)
  - intros. destruct (H H0 a b A a' b' A' R1 R1 eq_refl eq_refl) as (_ & P1 & P2 & P3).
    auto.
(*  - intros. destruct (H H2) as [T [P1 P2]].
    exists (a_Conv T R2 g_Triv); split; apply multipar_Cast_exists; auto. *)
Qed.


Lemma defeq_joins: forall S D A B T R, DefEq S D A B T R -> Good S D ->
                                         joins (ctx_to_rctx S) A B R.
Proof.
  apply consistent_mutual.
Qed.

Lemma defeq_consistent : forall S D A B T R, DefEq S D A B T R -> Good S D ->
                                        consistent A B R.
Proof. intros. eapply join_consistent. eapply defeq_joins; eauto.
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

Lemma consistent_Star : forall A0 R,
    consistent a_Star A0 R -> value_type R A0 -> A0 = a_Star.
Proof.
  intros A0 R C V.
  destruct A0; try destruct rho;
    simpl in *; inversion C; inversion V.
  all: subst; auto.
  all: try solve [inversion H].
  all: try solve [inversion H2].
  all: done.
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
    eapply defeq_consistent in h0; eauto;
    destruct (DefEq_lc H) as (l0 & l1 & l2); inversion l0; inversion l1; subst;
    have VT: value_type R A; eauto;
    have VT2 : value_type R B; eauto;
    inversion h0; subst;
    eauto; try done
  end.


Lemma canonical_forms_Star : forall G a R, Good G (dom G) ->
    Typing G a a_Star R -> Value R a -> value_type R a.
Proof.
  intros. induction H1; eauto.
  - assert False. eapply no_aAbs. eauto 2. done.
  - apply invert_a_UAbs in H0; eauto.
    destruct H0 as [A1 [B2 [H2 _]]].
    impossible_defeq. inversion H7.
  - apply invert_a_UAbs in H0; eauto.
    destruct H0 as (A1 & A2 & DE & A).
    impossible_defeq. inversion H6.
  - assert False. eapply no_aCAbs. eauto 2. done.
  - apply invert_a_UCAbs in H0; eauto.
    destruct H0 as [a0 [b [T [R1 [B1 [R2 [Q [P _]]]]]]]].
    impossible_defeq. inversion H7.
Qed.



Lemma DefEq_Star: forall A G D R, Good G D -> value_type R A ->
           DefEq G D A a_Star a_Star R -> A = a_Star.
Proof.
  intros.
  apply defeq_consistent in H1; eauto.
  inversion H1; eauto; subst; try done. inversion H3.
Qed.

Lemma canonical_forms_Pi : forall G rho a A R B R', Good G (dom G) ->
    Typing G a (a_Pi rho A R B) R' -> Value R' a ->
    (exists a1, a = a_UAbs rho R a1) \/ (exists F, Path F a R').
Proof.
  intros G rho a A R B R' C H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq.
    inversion H5.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq. inversion H7.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq. inversion H7.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & H & _); eauto.
    impossible_defeq. inversion H7.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & B1 & H & _); eauto.
    impossible_defeq. inversion H7.
  - assert False. eapply no_aCAbs. eauto 2. done.
  - eapply invert_a_UCAbs in H; eauto.
    destruct H as [a [b [T [R1 [B1 [_ [H _]]]]]]]; eauto.
    impossible_defeq. inversion H7.
Qed.

Lemma canonical_forms_CPi : forall G a phi B R, Good G (dom G) ->
    Typing G a (a_CPi phi B) R -> Value R a ->
    (exists a1, a = a_UCAbs a1) \/ (exists F, Path F a R).
Proof.
  intros G a phi B R C H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq. inversion H6.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq. inversion H8.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq. inversion H8.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [R' [H _]]]]; eauto.
    impossible_defeq. inversion H7.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [R' [H _]]]]; eauto.
    impossible_defeq. inversion H7.
  - assert False. eapply no_aCAbs. eauto 2. done.
Qed.



Definition irrelevant G D (a : tm) :=
  (forall x A R, binds x (Tm A R) G -> x `notin` fv_tm_tm_tm a) /\ Good G D.

Lemma irrelevant_Good : forall G D a, irrelevant G D a -> Good G D.
intros. inversion H.
auto.
Qed.

Lemma notin_sub : forall x a b, x `notin` a -> b [<=] a -> x `notin` b.
  intros. fsetdec.
Qed.

(*
   The progress lemma is stated in terms of the reduction_in_one relation,
   which is a subrelation of the Par relation.
*)

Lemma progress : forall G a A R, Typing G a A R ->
                          irrelevant G (dom G) a ->
                          Value R a \/ exists a', reduction_in_one a a' R.
Proof. intros. assert (lc_tm a). {eapply Typing_lc1; eauto. }
       induction H; eauto; try done.
  - destruct (IHTyping H0 H1) as [H3 | H4].
    eapply sub_Value; eauto.
    inversion H4. right. eapply sub_red_one; eauto.
  - unfold irrelevant in *.
    apply H0 in H2. simpl in H2. fsetdec.
  - left; econstructor; auto.
    inversion H1; auto.
  - destruct rho.
    + left. constructor; eauto.
    + pick fresh x. assert (x `notin` L). auto. move: (H4 x H5) => h0.
      inversion h0. subst. destruct (H2 x H5) as [V | [a' S]].
      { unfold irrelevant in H0. split_hyp.
      have ctx: (Ctx ([(x, Tm A R)] ++ G)) by eauto.
      move: (Ctx_uniq ctx) => u. inversion u. subst.
      split. intros. apply binds_cons_uniq_1 in H8. destruct H8.
      ++ split_hyp. subst. auto.
      ++ split_hyp. eapply notin_sub; [idtac|eapply fv_tm_tm_tm_open_tm_wrt_tm_upper].
         simpl in *. pose (Q := H0 x0 A0 R0 H8). apply notin_union_3; auto.
      ++ eauto.
      ++ simpl. eapply Good_add_tm_2; eauto using Typing_erased. }
      inversion H1; auto.
      -- left.
         eapply Value_UAbsIrrel_exists with (x := x); eauto.
      -- right. exists (a_UAbs Irrel R (close_tm_wrt_tm x a')).
         eapply E_AbsTerm_exists with (x := x).
         { eapply notin_union; auto.
           simpl. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto. }
         rewrite open_tm_wrt_tm_close_tm_wrt_tm. auto.
  - unfold irrelevant in H0. inversion H0.
    inversion H1; subst. destruct IHTyping1 as [V | [b' h0]]; auto 1.
    + unfold irrelevant in H0. inversion H0. split; auto.
      intros. pose (Q := H3 x A0 R0 H8). simpl in Q. eauto.
    + apply canonical_forms_Pi in H; auto.
      destruct H as [[a1 e1] | [F Q]]; subst. right.
      exists (open_tm_wrt_tm a1 a); eauto.
      left. eauto. 
    + right. exists (a_App b' Rel R a); eauto.
  - inversion H1; subst. unfold irrelevant in H0. inversion H0.
    case IHTyping1; auto.
    + split; auto. intros. pose (Q := H3 x A0 R0 H6). simpl in Q. eauto.
    + move => h1.  apply canonical_forms_Pi in H; auto.
      destruct H as [[a1 e1] | [F Q]]; subst. 
      right.
      exists (open_tm_wrt_tm a1 a_Bullet); eauto.

      left. eauto. 
    + move => h1. destruct h1 as [b' h0]. right.
      exists (a_App b' Irrel R a_Bullet); eauto.
  - left. constructor; eauto. inversion H1; auto.
  - inversion H1; subst. unfold irrelevant in H0. inversion H0.
    case IHTyping; auto.
    + split; auto. intros. pose (Q := H3 x A0 R0 H7). simpl in Q. eauto.
    + move => h1.  apply canonical_forms_CPi in H; auto.
      destruct H as [[a2 e1] | [F Q]]; subst. right.
      exists (open_tm_wrt_co a2 g_Triv); eauto.
      left. eauto.
    + intros H8. destruct H8 as [a' h0]. right.
      exists (a_CApp a' g_Triv); eauto.
  - destruct (sub_dec R R1) as [S1 | S2]. right; exists a; econstructor; eauto.
    left. eauto. 
Qed.


(* Generalizing progress *)

Lemma canonical_forms_Pi' : forall G rho a A R B R' R'', Good G (dom G) ->
    Typing G a (a_Pi rho A R B) R' -> Value R'' a ->
    (exists a1, a = a_UAbs rho R a1) \/ (exists F, Path F a R'').
Proof.
  intros G rho a A R B R' R'' C H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq.
    inversion H5.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq. inversion H7.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq. inversion H7.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & A2 & H & _); eauto.
    impossible_defeq. inversion H7.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as (A1 & B1 & H & _); eauto.
    impossible_defeq. inversion H7.
  - assert False. eapply no_aCAbs. eauto 2. done.
  - eapply invert_a_UCAbs in H; eauto.
    destruct H as [a [b [T [R1 [B1 [_ [H _]]]]]]]; eauto.
    impossible_defeq. inversion H7.
Qed.


Lemma canonical_forms_CPi' : forall G a phi B R R', Good G (dom G) ->
    Typing G a (a_CPi phi B) R -> Value R' a ->
    (exists a1, a = a_UCAbs a1) \/ (exists F, Path F a R').
Proof.
  intros G a phi B R R' C H H0.
  inversion H0; subst; eauto.
  - apply invert_a_Star in H; eauto.
    impossible_defeq. inversion H6.
  - eapply invert_a_Pi in H; eauto.
    destruct H as [H _]; eauto.
    impossible_defeq. inversion H8.
  - eapply invert_a_CPi in H; eauto.
    destruct H as [H _].
    impossible_defeq. inversion H8.
  - assert False. eapply no_aAbs. eauto 2. done.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [R'' [H _]]]]; eauto.
    impossible_defeq. inversion H7.
  - eapply invert_a_UAbs in H; eauto.
    destruct H as [A1 [A2 [R'' [H _]]]]; eauto.
    impossible_defeq. inversion H7.
  - assert False. eapply no_aCAbs. eauto 2. done.
Qed.


Lemma progress' : forall G a A R, Typing G a A R ->
                          irrelevant G (dom G) a -> forall R',
                          Value R' a \/ exists a', reduction_in_one a a' R'.
Proof. intros G a A R H H0. assert (lc_tm a). {eapply Typing_lc1; eauto. }
       induction H; eauto; try done. all: intros.
  - unfold irrelevant in *.
    apply H0 in H2. simpl in H2. fsetdec.
  - left; econstructor; auto.
    inversion H1; auto.
  - destruct rho. 
    + left. constructor; eauto.
    + pick fresh x. assert (x `notin` L). auto. move: (H4 x H5) => h0.
      inversion h0. subst. edestruct (H2 x H5) as [V | [a' S]].
      { unfold irrelevant in H0. split_hyp.
      have ctx: (Ctx ([(x, Tm A R)] ++ G)) by eauto.
      move: (Ctx_uniq ctx) => u. inversion u. subst.
      split. intros. apply binds_cons_uniq_1 in H8. destruct H8.
      ++ split_hyp. subst. auto.
      ++ split_hyp. eapply notin_sub; [idtac|eapply fv_tm_tm_tm_open_tm_wrt_tm_upper].
         simpl in *. pose (Q := H0 x0 A0 R0 H8). apply notin_union_3; auto.
      ++ eauto.
      ++ simpl. eapply Good_add_tm_2; eauto using Typing_erased. }
      inversion H1; auto.
      -- left.
         eapply Value_UAbsIrrel_exists with (x := x); eauto.
      -- right. exists (a_UAbs Irrel R (close_tm_wrt_tm x a')).
         eapply E_AbsTerm_exists with (x := x).
         { eapply notin_union; auto.
           simpl. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto. }
         rewrite open_tm_wrt_tm_close_tm_wrt_tm. auto.
  - unfold irrelevant in H0. inversion H0.
    inversion H1; subst. assert (irrelevant G (dom G) b).
    unfold irrelevant in H0. inversion H0. split; auto.
    intros. pose (Q := H3 x A0 R0 H8). simpl in Q. eauto.
    destruct (IHTyping1 H5 H7 R'0) as [V | [b' h0]]; auto 1.
    eapply canonical_forms_Pi' in H; eauto.
    destruct H as [[a1 e1] | [F Q]]; subst. right.
    exists (open_tm_wrt_tm a1 a); eauto.
    left. econstructor; eauto. right. exists (a_App b' Rel R a); eauto.
  - unfold irrelevant in H0. inversion H0.
    inversion H1; subst. assert (irrelevant G (dom G) b).
    unfold irrelevant in H0. inversion H0. split; auto.
    intros. pose (Q := H3 x A0 R0 H8). simpl in Q. eauto.
    destruct (IHTyping1 H5 H7 R'0) as [V | [b' h0]]; auto 1.
    eapply canonical_forms_Pi' in H; eauto.
    destruct H as [[a1 e1] | [F Q]]; subst. right.
    exists (open_tm_wrt_tm a1 a_Bullet); eauto.
    left. econstructor; eauto. right.
    exists (a_App b' Irrel R a_Bullet); eauto.
  - left. constructor; eauto. inversion H1; auto.
  - unfold irrelevant in H0. inversion H0.
    inversion H1; subst. assert (irrelevant G (dom G) a1).
    unfold irrelevant in H0. inversion H0. split; auto.
    intros. pose (Q := H3 x A0 R0 H9). simpl in Q. eauto.
    destruct (IHTyping H5 H7 R'0) as [V | [b' h0]]; auto 1.
    eapply canonical_forms_CPi' in H; eauto.
    destruct H as [[a2 e1] | [F Q]]; subst. right.
    exists (open_tm_wrt_co a2 g_Triv); eauto.
    left. econstructor; eauto. right. exists (a_CApp b' g_Triv); eauto.
  - destruct (sub_dec R R') as [S1 | S2]. right; exists a.
    econstructor; econstructor; eauto.
    left. eauto. 
Qed.


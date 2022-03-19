Require Export FcEtt.ett_ind.
Require Export FcEtt.tactics.
Require Export FcEtt.labels. 
Require Export FcEtt.weakening.
Require Export FcEtt.uniq.
Require Import FcEtt.ext_wf.

Set Implicit Arguments.
Open Scope grade_scope.


(* ----- Step ----- *)

(* does this still hold? *)
(* Lemma Step_substitution : forall b1 b2 a x, reduction_in_one b1 b2 -> lc_tm a -> reduction_in_one (tm_subst_tm_tm a x b1) (tm_subst_tm_tm a x b2). *)
(* Proof. *)
(*   intros. induction H. *)
(*   all: try solve [simpl; econstructor; eauto using tm_subst_tm_tm_lc_tm].  *)
(*   - simpl. *)
(*     rewrite tm_subst_tm_tm_open_tm_wrt_tm; auto. *)
(*      econstructor; eauto using tm_subst_tm_tm_lc_tm. *)
(*      match goal with [H : lc_tm (a_UAbs _ _) |- _ ] => inversion H end. subst. *)
(*      pick fresh y. *)
(*      eapply (lc_a_UAbs_exists y); eauto using tm_subst_tm_tm_lc_tm. *)
(*      replace (a_Var_f y) with (tm_subst_tm_tm a x (a_Var_f y)). *)
(*      rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto. *)
(*      eapply tm_subst_tm_tm_lc_tm; eauto. *)
(*      rewrite tm_subst_tm_tm_var_neq; auto. *)
(*   - simpl. *)
(*     econstructor; eauto using tm_subst_tm_tm_lc_tm. *)
(*     inversion H. subst. *)
(*      pick fresh y. *)
(*      eapply (lc_a_LetPair_exists y); eauto using subst_tm_tm_lc_tm. *)
(*      replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)). *)
(*      rewrite <- subst_tm_tm_open_tm_wrt_tm; auto. *)
(*      eapply subst_tm_tm_lc_tm; eauto. *)
(*      rewrite subst_tm_tm_var_neq; auto. *)
(*   - simpl. *)
(*     rewrite subst_tm_tm_open_tm_wrt_tm; auto. *)
(*     econstructor; eauto using subst_tm_tm_lc_tm. *)
(*     inversion H. subst. *)
(*      pick fresh y. *)
(*      eapply (lc_a_LetPair_exists y); eauto using subst_tm_tm_lc_tm. *)
(*      replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)). *)
(*      rewrite <- subst_tm_tm_open_tm_wrt_tm; auto. *)
(*      eapply subst_tm_tm_lc_tm; eauto. *)
(*      rewrite subst_tm_tm_var_neq; auto. *)
(* Qed. *)


(* --- grade --- *)

Lemma CGrade_Grade_lc :
  (forall P si b, Grade P si b -> lc_tm b) /\
  (forall P psi psi0 b, CGrade P psi psi0 b -> lc_tm b) /\
  (forall P psi phi, CoGrade P psi phi -> lc_constraint phi).
Proof. 
  apply CGrade_Grade_mutual.
  all: intros; split_hyp; eauto.
Qed.

Lemma Grade_lc : forall {P psi a}, Grade P psi a -> lc_tm a.
Proof. sfirstorder use:CGrade_Grade_lc. Qed.
Lemma CGrade_lc : forall {P psi phi a}, CGrade P psi phi a -> lc_tm a.
Proof. sfirstorder use:CGrade_Grade_lc. Qed.
Lemma CoGrade_lc : forall P psi phi, CoGrade P psi phi -> lc_constraint phi.
Proof. sfirstorder use:CGrade_Grade_lc. Qed.

Lemma Grade_CGrade: forall P phi psi a,  Grade P phi a -> CGrade P phi psi a.
Proof.
  intros.
  destruct (q_leb psi phi) eqn:LE.
  eapply CG_Leq; eauto. 
  eapply CG_Nleq; eauto using Grade_uniq, Grade_lc.
Qed.

Local Hint Resolve Grade_CGrade : core.

Ltac substitution_ih :=
    match goal with 
      | [H3 : forall P4 P3 x0 phi0,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P3 ++ [(x0, phi0)] ++ P4 -> _ |- _ ] => 
                specialize (H3 P1 ([(y, psi0)] ++ P2) x phi  ltac:(auto) _ ltac:(eauto)); 
        simpl_env in H3;
    autorewrite with subst_open_var; eauto using CGrade_lc;
    rewrite tm_subst_tm_tm_var_neq in H3
    end.

(* TODO: extend to include relevant coercions *)
Lemma CGrade_Grade_substitution_triv_CGrade : 
      (forall P psi b, 
          Grade P psi b -> forall P1 P2 c psi1, 
            P = P2 ++ [(c,psi1)] ++ P1 
            -> Grade (P2 ++ P1) psi (co_subst_co_tm g_Triv c b)) /\
      (forall P psi psi0 b,
      CGrade P psi psi0 b -> forall P1 P2 c psi1, 
        P = P2 ++ [(c,psi1)] ++ P1 
        -> CGrade (P2 ++ P1) psi psi0 (co_subst_co_tm g_Triv c b)) /\
      (forall P psi phi, CoGrade P psi phi -> forall P1 P2 c psi1,
      P = P2 ++ [(c,psi1)] ++ P1 -> CoGrade (P2 ++ P1) psi (co_subst_co_constraint g_Triv c phi)).
Proof.
  apply CGrade_Grade_mutual.
  all: intros; subst.
  all: try solve [simpl; eauto].
  all: try solve [eauto  using co_subst_co_tm_lc_tm, CGrade_lc] .
  - simpl.
    econstructor.
    solve_uniq.
    Search (binds _ _ (_ ++ _ ++ _)).
    apply binds_remove_mid in b; eauto.

    move : (utils.binds_cases _ _ _ _ _ _  u b).
    apply utils.binds_cases in b; eauto.
    
  all: try solve [simpl;
    fresh_apply_Grade y;
    eauto using co_subst_co_tm_lc_tm, CGrade_lc;
    repeat spec y;
    substitution_ih;
    eauto].

(* Possible to weaken CoGrade to something like: (psi0 <= psi -> ... /\ otherwise -> True)? *)
Lemma CGrade_Grade_substitution_CGrade : 
      (forall P psi b, 
          Grade P psi b -> forall P1 P2 x psi1, 
            P = P2 ++ [(x,psi1)] ++ P1 
            -> forall a, CGrade P1 psi psi1 a 
                   -> Grade (P2 ++ P1) psi (tm_subst_tm_tm a x b)) /\
      (forall P psi psi0 b,
      CGrade P psi psi0 b -> forall P1 P2 x psi1, 
        P = P2 ++ [(x,psi1)] ++ P1 
        -> forall a , CGrade P1 psi psi1 a 
        -> CGrade (P2 ++ P1) psi psi0 (tm_subst_tm_tm a x b)) /\
      (forall P psi phi, CoGrade P psi phi -> forall P1 P2 x psi1,
      P = P2 ++ [(x,psi1)] ++ P1 -> forall a, CGrade P1 psi psi1 a -> CoGrade (P2 ++ P1) psi (tm_subst_tm_constraint a x phi)).
Proof.
  apply CGrade_Grade_mutual. 
  all: intros; subst.
  all: try solve [simpl; eauto].
  all: try solve [eapply CG_Nleq; eauto  using tm_subst_tm_tm_lc_tm, CGrade_lc] .
  all: try solve [simpl;
    fresh_apply_Grade y;
    eauto using tm_subst_tm_tm_lc_tm, CGrade_lc;
    repeat spec y;
    substitution_ih;
    eauto].
  - (* Var *) 
    destruct (x == x0).
    + subst.
      apply binds_mid_eq in b; auto. subst.
      rewrite tm_subst_tm_tm_var; auto.
      eapply Grade_weakening; try solve_uniq.
      match goal with [ H : CGrade _ _ _ _ |- _ ] => inversion H; clear H; subst end; auto; try done.
    + rewrite tm_subst_tm_tm_var_neq. auto.
      apply binds_remove_mid in b; auto.
      eapply G_Var; eauto.
      assumption.
Qed.

Lemma Grade_substitution_CGrade : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> CGrade P1 psi phi a 
    -> Grade (P2 ++ P1) psi (tm_subst_tm_tm a x b).
Proof. 
  intros.
  eapply CGrade_Grade_substitution_CGrade; eauto. Qed.

Lemma Grade_substitution_same : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> Grade P1 psi a 
    -> Grade (P2 ++ P1) psi (tm_subst_tm_tm a x b).
Proof. 
  intros.
  eapply Grade_substitution_CGrade; eauto.
Qed.

Lemma CoGrade_substitution_CGrade : forall P2 x psi0 P1 psi a phi,
      CoGrade (P2 ++ x ~ psi0 ++ P1) psi phi
    -> CGrade P1 psi psi0 a 
    -> CoGrade (P2 ++ P1) psi (tm_subst_tm_constraint a x phi).
Proof. 
  intros.
  eapply CGrade_Grade_substitution_CGrade; eauto.
Qed.

  
Lemma Grade_substitution_irrel : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> not (phi <= psi)
    -> lc_tm a
    -> Grade (P2 ++ P1) psi (tm_subst_tm_tm a x b).
Proof. 
  intros.
  eapply Grade_substitution_CGrade; eauto.
  eapply Grade_uniq in H. destruct_uniq.
  eauto.
Qed.

Lemma Grade_open : forall P psi y psi0 a b,
  y `notin` fv_tm_tm_tm a ->
  Grade P psi b ->
  Grade ([(y, psi0)] ++ P) psi (open_tm_wrt_tm a (a_Var_f y)) -> 
  Grade P psi (open_tm_wrt_tm a b).
Proof.
  intros.
  move: (Grade_substitution_same nil _ _ H1 H0) => ss.
  rewrite tm_subst_tm_tm_open_tm_wrt_tm in ss;
  eauto using Grade_lc.
  rewrite tm_subst_tm_tm_var in ss.
  rewrite tm_subst_tm_tm_fresh_eq in ss; auto.
Qed.

Lemma Grade_open_irrel : forall P psi y psi0 a b,
  y `notin` fv_tm_tm_tm a ->
  not (psi0 <= psi) ->
  lc_tm b ->
  Grade ([(y, psi0)] ++ P) psi (open_tm_wrt_tm a (a_Var_f y)) -> 
  Grade P psi (open_tm_wrt_tm a b).
Proof.
  intros.
  move: (Grade_substitution_irrel nil _ _ H2 ltac:(auto) H1) => ss.
  rewrite tm_subst_tm_tm_open_tm_wrt_tm in ss;
  eauto using Grade_lc.
  rewrite tm_subst_tm_tm_var in ss.
  rewrite tm_subst_tm_tm_fresh_eq in ss; auto.
Qed.

Lemma Grade_renaming : forall y x psi0 P psi b1, 
    x `notin` dom P \u fv_tm_tm_tm b1 -> 
    y `notin` dom P \u fv_tm_tm_tm b1 \u {{x}} -> 
    Grade ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) -> 
    Grade ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)).
Proof.
  intros.
  rewrite (tm_subst_tm_tm_intro y b1); auto.
  move: (Grade_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply Grade_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
    eapply Grade_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply Grade_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto.
    eapply Grade_weakening_middle; eauto. 
    auto.
Qed. 

Ltac exists_apply_Grade x :=
  let y := fresh in
  fresh_apply_Grade y; eauto;
  eapply (@Grade_renaming x); try rewrite fv_tm_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.

(* --- geq --- *)


Ltac invert_Grade := 
  match goal with 
      | [ H : Grade ?P ?psi (a_Var_f ?x) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Pi ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_CPi ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_UAbs ?psi2 ?b) |- _  ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_UCAbs ?psi2 ?b) |- _  ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_App ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_CApp ?a ?b) |- _ ] => inversion H ; clear H
    end.


Lemma CEq_GEq_equality_substitution : 
  (forall P psi psi0 b1 b2,
  CEq P psi psi0 b1 b2 ->  forall P1 P2 x psi1, 
        P = P2 ++ [(x,psi1)] ++ P1 
       -> forall a1 a2, CEq P1 psi psi1 a1 a2 
       -> CEq (P2 ++ P1) psi psi0 (tm_subst_tm_tm a1 x b1) (tm_subst_tm_tm a2 x b2)) /\
  (forall P psi b1 b2,
  GEq P psi b1 b2 -> forall P1 P2 x psi1, 
        P = P2 ++ [(x,psi1)] ++ P1 
       -> forall a1 a2, CEq P1 psi psi1 a1 a2  
       -> GEq (P2 ++ P1) psi (tm_subst_tm_tm a1 x b1) (tm_subst_tm_tm a2 x b2)) /\
  (forall P psi phi1 phi2,
  CoGEq P psi phi1 phi2 -> forall P1 P2 x psi1,
        P = P2 ++ [(x,psi1)] ++ P1
       -> forall a1 a2, CEq P1 psi psi1 a1 a2
       -> CoGEq (P2 ++ P1) psi (tm_subst_tm_constraint a1 x phi1) (tm_subst_tm_constraint a2 x phi2)).
Proof. 
  apply CEq_GEq_mutual.
  all: intros; subst; eauto.  
  all: try solve [simpl; eauto].
  all: try solve [
    repeat invert_Grade; subst;
    simpl; fresh_apply_GEq y; eauto;
    repeat spec y;
    match goal with 
      [ 
         H5 : forall P3 P4 x0 psi1,  
          [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?psi2)] ++ ?P1 = P4 ++ [(x0, psi1)] ++ P3 -> _ 
          |- _ ] => 
    specialize (H5 P1 ([(y, psi0)] ++ P2) x psi2 ltac:(auto) _ _ ltac:(eauto 3));
    simpl_env in H5;
    simpl_env in H5;
    autorewrite with open_subst_var in *; eauto 3 using CEq_lc1, CEq_lc2, CoGEq_lc1, CoGEq_lc2;
    repeat rewrite tm_subst_tm_tm_var_neq in H5; eauto
    end] .
  - (* Var *)
    destruct (x == x0).
    + subst.
      repeat rewrite tm_subst_tm_tm_var.
      match goal with [ H : CEq _ _ _ _ _ |- _ ] => inversion H; subst end.
      ++ (* 
            psi0 <= psi -- 
          *)
        eapply GEq_weakening; eauto.        
      ++
        apply binds_mid_eq in b; auto. subst.
        done.
        (* 
            here we know that not (psi0 <= psi). 
          *)
    + repeat rewrite tm_subst_tm_tm_var_neq; eauto.
  - hauto l: on ctrs: CEq use: CEq_GEq_lc, tm_subst_tm_tm_lc_tm.
Qed.


Lemma GEq_open: forall P psi psi0 a1 a2 a b0 x, 
      x \notin fv_tm_tm_tm a -> x \notin fv_tm_tm_tm b0 ->
      CEq P psi psi0 a1 a2 ->
      GEq ([(x, psi0)] ++ P) psi (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b0 (a_Var_f x)) ->
      GEq P psi (open_tm_wrt_tm a a1) (open_tm_wrt_tm b0 a2).
Proof.
      intros.
      move: (CEq_GEq_equality_substitution) => [_ [h1 _]].
      specialize (h1 _ _  _ _ H2 P nil x psi0 ltac:(eauto) _ _ H1).
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in h1; eauto 3 using CEq_lc1, CEq_lc2.
      repeat rewrite tm_subst_tm_tm_var in h1.
      repeat rewrite tm_subst_tm_tm_fresh_eq in h1; auto.
Qed.

Lemma CEq_GEq_refl : 
  (forall P phi a, Grade P phi a -> GEq P phi a a) /\
  (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a a) /\
  (forall P psi phi, CoGrade P psi phi -> CoGEq P psi phi phi).
Proof. 
  apply CGrade_Grade_mutual.
  all: sfirstorder.
Qed.

Lemma GEq_refl : forall P phi a, Grade P phi a -> GEq P phi a a.
  intros. eapply CEq_GEq_refl. auto.
Qed.

Lemma CEq_refl : forall P phi a psi, Grade P phi a -> CEq P phi psi a a.
Proof.
  intros.
  destruct (q_leb psi phi) eqn:LE.
  + eapply CEq_Leq; eauto.
    eapply GEq_refl; eauto.
  + eapply CEq_Nleq; eauto using Grade_uniq, Grade_lc.
Qed.


Lemma GEq_substitution_same : forall P1 P2 x psi phi b1 b2 a,
  GEq (P2 ++ [(x,psi)] ++ P1) phi b1 b2 
  -> Grade P1 phi a
  -> GEq (P2 ++ P1) phi (tm_subst_tm_tm a x b1) (tm_subst_tm_tm a x b2). 
Proof.
  hauto lq: on use: CEq_GEq_equality_substitution, CEq_refl.
Qed.

Lemma GEq_substitution_irrel : forall P1 P2 x psi phi b1 b2 a1 a2,
  GEq (P2 ++ [(x,psi)] ++ P1) phi b1 b2 
  -> not (psi <= phi)
  -> lc_tm a1
  -> lc_tm a2
  -> GEq (P2 ++ P1) phi (tm_subst_tm_tm a1 x b1) (tm_subst_tm_tm a2 x b2). 
Proof.
  intros.
  move: CEq_GEq_equality_substitution => [_ h].
  eapply h; eauto.
  eapply CEq_Nleq; eauto.
  move: (GEq_uniq H) => u. solve_uniq.
Qed.

Lemma GEq_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 -> 
    y `notin` dom P \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u {{x}} -> 
    GEq ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) -> 
    GEq ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (tm_subst_tm_tm_intro y b1); auto.
  rewrite (tm_subst_tm_tm_intro y b2); auto.
  move: (GEq_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply GEq_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
    eapply GEq_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply GEq_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); auto; simpl_env. 
    eapply GEq_weakening_middle; eauto. 
    rewrite LE. done.
Qed. 

Ltac exists_apply_GEq x :=
  let y := fresh in
  fresh_apply_GEq y; eauto;
  eapply (@GEq_renaming x); try rewrite fv_tm_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.


(* --- defeq ---- *)

Local Ltac defeq_subst_ih :=  match goal with 
      [ 
         H5 : forall P3 P4 x0 psi1,  
          [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?psi2)] ++ ?P1 = P4 ++ [(x0, psi1)] ++ P3 -> _ 
          |- _ ] => 
    specialize (H5 P1 ([(y, psi0)] ++ P2) x psi2 ltac:(auto) _ ltac:(eauto 3));
    simpl_env in H5;
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in H5; eauto 3 using CGrade_lc;
    repeat rewrite tm_subst_tm_tm_var_neq in H5; eauto end.

(* TODO: move to ext_subst.v *)
(* Lemma CDefEq_DefEq_substitution_CGrade :  *)
(*   (forall P phi phi0 b1 b2, CDefEq P phi phi0 b1 b2 -> forall P1 P2 x psi,  *)
(*         P = P2 ++ [(x,psi)] ++ P1  *)
(*        -> forall a, CGrade P1 phi psi a *)
(*        -> CDefEq (P2 ++ P1) phi phi0 (tm_subst_tm_tm a x b1) (subst_tm_tm a x b2)) /\ *)
(*   (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi,  *)
(*         P = P2 ++ [(x,psi)] ++ P1  *)
(*        -> forall a, CGrade P1 phi psi a *)
(*        -> DefEq (P2 ++ P1) phi (subst_tm_tm a x b1) (subst_tm_tm a x b2)).  *)
(* Proof.  *)
(*   apply CDefEq_DefEq_mutual. *)
(*   all: intros; subst.   *)
(*   all: try solve [eapply Eq_Refl; eauto using Grade_substitution_CGrade]. *)
(*   all: try solve [eapply Eq_Beta; eauto using Grade_substitution_CGrade, Step_substitution, CGrade_lc]. *)
(*   all: try solve [simpl; eapply Eq_App; eauto using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc]. *)
(*   all: try solve [simpl; eapply Eq_WPair; eauto using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc]. *)
(*   all: try solve [simpl; eapply Eq_SPair; eauto using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc]. *)
(*   all: try solve [repeat invert_Grade; subst; *)
(*     simpl; fresh_apply_DefEq y; eauto 3 using subst_tm_tm_lc_tm, CGrade_lc; *)
(*     repeat spec y; *)
(*     defeq_subst_ih] . *)
(*   all: try solve [simpl; eauto 3]. *)
(*   eapply Eq_Trans; eauto 2. *)
(*   all: try solve [simpl; eauto 4 using Grade_substitution_CGrade, Step_substitution, CGrade_lc]. *)
(*   - eapply Eq_PiFst; eauto 1.  *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ ltac:(eauto)); *)
(*     simpl in H; eauto. *)
(*   - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc. *)
(*     match goal with [H2 : CGrade _ _ _ _|- _ ] =>  *)
(*     specialize (H0 _ _ _ _ ltac:(eauto) _ H2); *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ H2) end. simpl in H0. *)
(*     eapply Eq_PiSnd; eauto 3 using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc.     *)
(*   - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc. *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ H1); simpl in H; eauto. *)
(*   - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc. *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ H1); simpl in H. *)
(*     eapply Eq_WSigmaSnd; eauto using Grade_substitution_CGrade. *)
(*   - specialize (H _ _ _ _ ltac:(eauto) _ H1); simpl in H. *)
(*     eapply Eq_SSigmaFst; eauto using Grade_substitution_CGrade. *)
(*   - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc. *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ H2); simpl in H. *)
(*     eapply Eq_SSigmaSnd; eauto using Grade_substitution_CGrade. *)
(*   - eapply Eq_SumFst; eauto 1.   *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ ltac:(eauto)); *)
(*     simpl in H; eauto. *)
(*   - eapply Eq_SumSnd; eauto 1.   *)
(*     specialize (H _ _ _ _ ltac:(eauto) _ ltac:(eauto)); *)
(*     simpl in H; eauto. *)
(*   - simpl. *)
(*     eapply Eq_Case; eauto. *)
(*   - repeat invert_Grade; subst; *)
(*     simpl. *)
(*     repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc. *)
(*     pick fresh y and apply Eq_SubstIrrel; eauto 2.  *)
(*     eauto using subst_tm_tm_lc_tm, CGrade_lc.     *)
(*     eauto using subst_tm_tm_lc_tm, CGrade_lc.     *)
(*     repeat spec y. *)
(*     specialize (H2 P1 ([(y, psi)] ++ P2) x psi0). *)
(*     simpl_env in H2. specialize (H2 ltac:(auto)). *)
(*     specialize (H2 _ ltac:(eassumption)). *)
(*     repeat rewrite subst_tm_tm_open_tm_wrt_tm in H2; eauto 2 using CGrade_lc. *)
(*     rewrite subst_tm_tm_var_neq in H2. auto. *)
(*     auto. *)
(*   - eapply CDefEq_Nleq; eauto using subst_tm_tm_lc_tm, CGrade_lc. *)
(* Qed. *)

(* Lemma DefEq_substitution_CGrade :  *)
(*   (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi,  *)
(*         P = P2 ++ [(x,psi)] ++ P1  *)
(*        -> forall a, CGrade P1 phi psi a *)
(*        -> DefEq (P2 ++ P1) phi (subst_tm_tm a x b1) (subst_tm_tm a x b2)).  *)
(* Proof. *)
(*   intros.  *)
(*   eapply CDefEq_DefEq_substitution_CGrade; eauto. *)
(* Qed. *)

(* Lemma DefEq_substitution_same :  *)
(*   (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi,  *)
(*         P = P2 ++ [(x,psi)] ++ P1  *)
(*        -> forall a, Grade P1 phi a *)
(*        -> DefEq (P2 ++ P1) phi (subst_tm_tm a x b1) (subst_tm_tm a x b2)).  *)
(* Proof.  *)
(*   intros. *)
(*   eapply DefEq_substitution_CGrade; eauto. *)
(* Qed. *)

(* Lemma DefEq_substitution_irrel : forall (P : econtext) (psi : grade) (b1 b2 : tm), *)
(*        DefEq P psi b1 b2 -> *)
(*        forall (P1 P2 : list (atom * grade)) (x : atom) (phi : grade), *)
(*        P = P2 ++ [(x, phi)] ++ P1 -> *)
(*        not (phi <= psi) -> *)
(*        forall a : tm, lc_tm a -> DefEq (P2 ++ P1) psi (subst_tm_tm a x b1) (subst_tm_tm a x b2). *)
(* Proof.  *)
(*   intros. *)
(*   eapply DefEq_substitution_CGrade; eauto. *)
(*   subst. apply DefEq_uniq in H. destruct_uniq. *)
(*   auto. *)
(* Qed. *)


(* Lemma DefEq_renaming : forall y x psi0 P psi b1 b2,  *)
(*     x `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 ->  *)
(*     y `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 \u {{x}} ->  *)
(*     DefEq ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) ->  *)
(*     DefEq ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)). *)
(* Proof. *)
(*   intros. *)
(*   rewrite (subst_tm_tm_intro y b1); auto. *)
(*   rewrite (subst_tm_tm_intro y b2); auto. *)
(*   move: (DefEq_uniq H1) => u.  *)
(*   destruct (q_leb psi0 psi) eqn:LE. *)
(*   - eapply DefEq_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto. *)
(*     eapply DefEq_weakening_middle; eauto.  *)
(*     eapply G_Var; eauto. *)
(*     solve_uniq. *)
(*   - eapply DefEq_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto. *)
(*     eapply DefEq_weakening_middle; eauto.  *)
(*     rewrite LE. done. *)
(*     auto. *)
(* Qed.  *)

(* Ltac exists_apply_DefEq x := *)
(*   let y := fresh in *)
(*   fresh_apply_DefEq y; eauto; *)
(*   eapply (@DefEq_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto; *)
(*   rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto. *)


(* --- par ---- *)


(* Local Ltac par_subst2_ih := *)
(*     match goal with  *)
(*       | [H3 : forall P3 x0 phi0 P4, *)
(*             (?y, ?psi0) :: ?P2 ++ (?x, ?phi) :: ?P1 = P3 ++ (x0, phi0) ::  P4 -> _ |- _ ] =>  *)
(*     specialize (H3 ([(y, psi0)] ++ P2) x phi P1 ltac:(reflexivity) _ ltac:(eassumption)); *)
(*     simpl_env in H3; *)
(*     repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using CGrade_lc, Par_lc1, Par_lc2; *)
(*     repeat rewrite tm_subst_tm_tm_var_neq in H3  *)
(*     end. *)

(* Lemma CPar_Par_substitution_CGrade : (forall P psi psi0 a a',  *)
(*   CPar P psi psi0 a a' -> forall P2 x phi P1, P = (P2 ++ [(x, phi)] ++ P1) -> *)
(*   forall b, CGrade P1 psi phi b -> *)
(*   CPar (P2 ++ P1) psi psi0 (subst_tm_tm b x a) (subst_tm_tm b x a')) /\ (forall P psi a a',  *)
(*   Par P psi a a' -> forall P2 x phi P1, P = (P2 ++ [(x, phi)] ++ P1) -> *)
(*   forall b, CGrade P1 psi phi b -> *)
(*   Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b x a')). *)
(* Proof. *)
(*   apply CPar_Par_mutual. *)
(*   all: simpl; intros; subst. *)
(*   all: simpl; eauto using Grade_substitution_CGrade, GEq_substitution_same, GEq_substitution_irrel. *)
(*   (* 9 subgoals *) *)
(*   all: repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CGrade_lc. *)
(*   all: try solve [fresh_apply_Par y; eauto; repeat spec y; *)
(*             par_subst2_ih; eauto]. *)
(*   (* 2 subgoals *) *)
(*   - simpl_env in *. eapply Par_Refl; eauto using Grade_substitution_CGrade. *)
(*   - simpl_env in *. eapply CPar_Nleq; eauto using CGrade_lc, subst_tm_tm_lc_tm. *)
(* Qed. *)

(* Lemma Par_substitution_CGrade : forall P2 x phi P1 psi a a',  *)
(*   Par (P2 ++ [(x, phi)] ++ P1) psi a a' ->  *)
(*   forall b, CGrade P1 psi phi b -> *)
(*   Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b x a'). *)
(* Proof. intros. eapply CPar_Par_substitution_CGrade; eauto. Qed. *)

(* Lemma subst2 : forall x phi P1 psi a a' b,  *)
(*   Par ([(x, phi)] ++ P1) psi a a' ->  *)
(*   Grade P1 psi b -> *)
(*   Par P1 psi (subst_tm_tm b x a) (subst_tm_tm b x a'). *)
(* Proof. intros. eapply Par_substitution_CGrade with (P2:=nil); eauto. Qed. *)

(* Lemma subst2_irrel : forall x phi P1 psi a a',  *)
(*   Par ([(x, phi)] ++ P1) psi a a' ->  *)
(*   forall b, not (phi <= psi) -> *)
(*   lc_tm b -> *)
(*   Par P1 psi (subst_tm_tm b x a) (subst_tm_tm b x a'). *)
(* Proof. *)
(*   intros. *)
(*   eapply Par_substitution_CGrade with (P2:=nil); eauto.  *)
(*   apply Par_uniq in H. destruct_uniq. *)
(*   eapply CG_Nleq; eauto. *)
(* Qed. *)

(* Lemma Par_renaming : forall y x psi0 P psi b1 b2,  *)
(*     x `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 ->  *)
(*     y `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 \u {{x}} ->  *)
(*     Par ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) ->  *)
(*     Par ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)). *)
(* Proof. *)
(*   intros. *)
(*   rewrite (subst_tm_tm_intro y b1); auto. *)
(*   rewrite (subst_tm_tm_intro y b2); auto. *)
(*   move: (Par_uniq H1) => u.  *)
(*   destruct (q_leb psi0 psi) eqn:LE. *)
(*   - eapply subst2; eauto. *)
(*     eapply Par_weakening_middle; eauto.  *)
(*     eapply G_Var; eauto. *)
(*     solve_uniq. *)
(*   - eapply subst2_irrel; eauto. *)
(*     eapply Par_weakening_middle; eauto.  *)
(*     rewrite LE. done. *)
(* Qed.  *)

(* Ltac exists_apply_Par x := *)
(*   let y := fresh in *)
(*   fresh_apply_Par y; eauto; *)
(*   eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto; *)
(*   rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto. *)

(* (* Par / CPar substitution *) *)

(* Local Ltac subst5_ih := *)
(*     match goal with  *)
(*       | [H3 : forall P3 P4 x0 phi0, *)
(*             [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 ~= P4 ++ [(x0, phi0)] ++ P3 -> _ |- _ ] =>  *)
(*     specialize (H3 P1 ([(y, psi0)] ++ P2) x phi ltac:(reflexivity) _ _ ltac:(eassumption)); *)
(*     simpl_env in H3; *)
(*     repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2; *)
(*     repeat rewrite subst_tm_tm_var_neq in H3  *)
(*     end. *)

(* Lemma subst5_full : *)
(*  (forall P psi psi0 a a', *)
(*   CEq P psi psi0 a a' ->  forall P1 P2 x phi, *)
(*         P = P2 ++ [(x,phi)] ++ P1  *)
(*        -> forall b b', CPar P1 psi phi b b'  *)
(*        -> CPar (P2 ++ P1) psi psi0 (subst_tm_tm b x a) (subst_tm_tm b' x a')) /\ *)
(*   (forall P psi a a', *)
(*   GEq P psi a a' -> forall P1 P2 x phi,  *)
(*         P = P2 ++ [(x,phi)] ++ P1  *)
(*        -> forall b b', CPar P1 psi phi b b'  *)
(*        -> Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b' x a')). *)
(* Proof. *)
(*   eapply CEq_GEq_mutual. *)
(*   all: intros; subst; simpl; eauto.   *)

(*   destruct (x == x0); subst; *)
(*   [  inversion H0; subst; eapply Par_weakening; eauto; *)
(*     apply binds_mid_eq in b; auto; subst; done *)
(*   | eauto]. *)

(*   all: try move: (CEq_uniq c) => U; destruct_uniq. *)

(*   all : try solve [ *)
(*   fresh_apply_Par y; eauto 3; repeat spec y; *)
(*   match goal with  *)
(*       | [H3 : forall P3 P4 x0 phi0, *)
(*             [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P4 ++ [(x0, phi0)] ++ P3 -> _ |- _ ] =>  *)
(*     specialize (H3 P1 ([(y, psi0)] ++ P2) x phi ltac:(reflexivity) _ _ ltac:(eassumption)); *)
(*     simpl_env in H3; *)
(*     repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2; *)
(*     repeat rewrite subst_tm_tm_var_neq in H3 end; eauto 3 ]. *)
(*   eapply CPar_Nleq; eauto 3 using CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm. *)
(* Qed. *)


(* Lemma Par_subst3_full : forall P1 psi phi b b', *)
(*     CPar P1 psi phi b b' -> *)
(*     ((forall P psi1 psi0 a a', CPar P psi1 psi0 a a' -> forall P2 x, P = (P2 ++ [(x,phi)] ++ P1) -> psi = psi1 ->  *)
(*     CPar (P2 ++ P1) psi1 psi0 (subst_tm_tm b x a) (subst_tm_tm b' x a'))) /\  *)
(*     (forall P psi1 a a', Par P psi1 a a' -> forall P2 x, P = (P2 ++ [(x,phi)] ++ P1) -> psi = psi1 -> *)
(*     Par (P2 ++ P1) psi1 (subst_tm_tm b x a) (subst_tm_tm b' x a')). *)
(* Proof. *)
(*   intros. *)
(*   apply CPar_Par_mutual. *)
(*   all: intros; subst; simpl; eauto 4. *)
(*   (* refl case *) *)
(*   move: (subst5_full) => [_ h].  *)
(*   eapply h; eauto using GEq_refl. *)

(*   all: repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using  CPar_lc1, CPar_lc2. *)
(*   all: eauto. *)
(* (*  all: try (eapply_ParIrrel; eauto 3 using CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm).   *) *)

(*   all: try solve [ *)
(*   fresh_apply_Par y; eauto 3; repeat spec y; *)
(*   match goal with  *)
(*       | [H3 : forall P3 x0, *)
(*             [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P3 ++ [(x0, ?phi0)] ++ ?P5 -> _ |- _ ] =>  *)
(*     specialize (H3 ([(y, psi0)] ++ P2) x ltac:(reflexivity) ltac:(reflexivity)); *)
(*     simpl_env in H3; *)
(*     repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2; *)
(*     repeat rewrite subst_tm_tm_var_neq in H3 end; eauto 3]. *)

(*   destruct_uniq. *)
(*  eapply CPar_Nleq; eauto 3 using CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm. *)
(* Qed. *)

(* Lemma Par_subst3 : forall P1 phi b psi b' x, *)
(*     CPar P1 psi phi b b' -> *)
(*     forall a a', Par ([(x,phi)] ++ P1) psi a a' -> *)
(*     Par P1 psi (subst_tm_tm b x a) (subst_tm_tm b' x a'). *)
(* Proof. *)
(*   intros. *)
(*   eapply Par_subst3_full with (P2 := nil); eauto. *)
(* Qed. *)

(* --------------------------- *)

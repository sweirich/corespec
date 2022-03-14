Require Import Metalib.Metatheory.

Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.imports.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(*

This module proves the following results:

     Lemma AnnSig_an_toplevel: AnnSig an_toplevel.
     Lemma Sig_toplevel: Sig toplevel.


It *should* be the only place in the development that
unfolds the definition of an_toplevel. That way, if we change the
definition of the signature in ett.ott, we only need to change this file.

In this case, it uses the fact that an_toplevel (defined in ett.ott)
contains the following definitions:

Definition Fix : atom.
  pick fresh F.
  exact F.
Qed.

Definition FixDef : tm :=
  (a_Abs Irrel a_Star
         (a_Abs Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1))
                (a_App (a_Var_b 0) Rel
                       (a_App (a_App (a_Fam Fix) Irrel (a_Var_b 1)) Rel (a_Var_b 0))))).

Definition FixTy : tm :=
  a_Pi Irrel a_Star
       (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1))
             (a_Var_b 1)).
 *)

Lemma AxFix : binds Fix (q_R, (Ax FixDef FixTy)) an_toplevel.
  unfold an_toplevel.
  eauto.
Qed.

Ltac an_use_binder f x :=
  pick fresh x and apply f; eauto;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- AnnTyping ?ctx ?psi ?a ?A ] =>
    assert (AnnCtx ctx); [econstructor; eauto|idtac]
  end.

Local Open Scope grade_scope.
Lemma An_App_intro :
  forall (G : context) (b : tm) (psi psi0 : grade) (a B A C : tm),
       (psi0 <= q_C) ->
       AnnTyping G psi b (a_Pi psi0 A B) -> (open_tm_wrt_tm B a) = C ->
       AnnTyping G (q_join psi0 psi) a A -> AnnTyping G psi (a_App b psi0 a) C.
Proof.
  hauto lq: on ctrs: AnnTyping.
Qed.

Create HintDb l1_lattice.
Create HintDb lattice_props.

Ltac solve_lattice := sfirstorder ctrs: AnnTyping
       use: join_idem, join_leq, meet_comm, meet_leq, meet_idem, R_lt_C, join_comm, q_leb_refl, join_Top_r, leq_Top.

Lemma C_join_R : q_C * q_R = q_C.
Proof.
  solve_lattice.
Qed.

Lemma R_join_C : q_R * q_C = q_C.
Proof.
  solve_lattice.
Qed.

Lemma C_join_C : q_C * q_C = q_C.
Proof.
  solve_lattice.
Qed.

Lemma R_join_R : q_R * q_R = q_R.
Proof.
  solve_lattice.
Qed.

Lemma C_meet_R : q_C + q_R = q_R.
Proof.
  solve_lattice.
Qed.

Lemma R_meet_C : q_R + q_C = q_R.
Proof.
  solve_lattice.
Qed.

Lemma C_meet_C : q_C + q_C = q_C.
Proof.
  solve_lattice.
Qed.

Lemma R_meet_R : q_R + q_R = q_R.
Proof.
  solve_lattice.
Qed.


Hint Resolve join_idem join_leq meet_comm meet_leq meet_idem R_lt_C join_comm q_leb_refl join_Top_r leq_Top q_leb_trans q_leb_antisym : lattice_props.
Hint Rewrite C_join_R R_join_C C_join_C R_join_R C_meet_R R_meet_C C_meet_C R_meet_R join_idem_l join_Top_l join_assoc join_Top_r join_idem : l1_lattice.


Lemma FixTy_Star :
  AnnTyping nil q_C FixTy a_Star.
Proof.
  an_use_binder An_Pi X.
  an_use_binder An_Pi Z.
  an_use_binder An_Pi W.

  hfcrush ctrs: AnnTyping.
  all : try solve [qauto ctrs: AnnTyping use: meet_idem, q_leb_refl].
  an_use_binder An_Pi W.
  all : solve [qauto ctrs: AnnTyping use: meet_idem, q_leb_refl].
Qed.




Lemma FixDef_FixTy :
  AnnTyping nil q_R FixDef FixTy.
Proof.
  an_use_binder An_Abs X.
  an_use_binder An_Abs x.
  { an_use_binder An_Pi Z.
    simpl.
    apply An_Var with (psi0 := q_C);
    hecrush ctrs: AnnTyping db: l1_lattice.
    qauto l: on ctrs: AnnTyping use: join_leq, meet_leq, meet_idem, R_lt_C, join_comm, q_leb_refl.
    qauto l: on ctrs: AnnTyping use: join_leq, meet_leq, meet_idem, R_lt_C, join_comm, q_leb_refl.
       }
   { an_use_binder An_Pi Z;  simpl in *;autorewrite with l1_lattice in *.
     hfcrush ctrs: AnnTyping use: join_leq, meet_leq, meet_idem, R_lt_C, join_comm, q_leb_refl.
     simpl.
     apply An_Var with (psi0 := q_C);
       hfcrush l: on ctrs: AnnTyping use: join_leq, meet_leq, meet_idem, R_lt_C, join_comm, q_leb_refl.
     apply An_Var with (psi0 := q_C); solve_lattice.
     apply An_Var with (psi0 := q_C); solve_lattice.
   }
   { eapply An_App_intro; eauto; try solve_lattice.
     (* Var *)
     apply An_Var with (psi0 := q_R).
     assumption.
     2 : solve_lattice.
     all : autorewrite with l1_lattice in *; eauto.
    { autorewrite with l1_lattice.
      eapply An_App_intro; simpl in *; autorewrite with l1_lattice in *; try solve_lattice.
      { eapply An_App_intro; simpl in *; autorewrite with l1_lattice in *; try solve_lattice.
        econstructor; eauto.
        apply q_leb_refl.
        unfold an_toplevel.
        eapply AxFix.
        an_use_binder An_Pi Z.
        an_use_binder An_Pi W; eauto.
        an_use_binder An_Pi M; eauto.
        all : simpl in *;autorewrite with l1_lattice in *; eauto.
        all : try solve [apply An_Var with (psi0 := q_C); eauto; solve_lattice].
        an_use_binder An_Pi N; eauto.
        unfold open_tm_wrt_tm. simpl. autorewrite with l1_lattice in *; eauto.
        all : try solve [apply An_Var with (psi0 := q_C); eauto; solve_lattice].
        unfold open_tm_wrt_tm. simpl. eauto.
      }
      unfold open_tm_wrt_tm. simpl. eauto.
      apply An_Var with (psi0 := q_R); solve_lattice.
    }
  }
Qed.

Lemma AnnSig_an_toplevel: AnnSig an_toplevel.
Proof.
  best ctrs: AnnSig use: FixTy_Star, FixDef_FixTy.
Qed.

(* ---------------------------------------------------------- *)

Ltac use_binder f x :=
  pick fresh x and apply f;
  unfold open_tm_wrt_tm; simpl; simpl_env; eauto;
  match goal with
    [ |- Typing ?ctx ?psi ?a ?A ] =>
    assert (Ctx ctx); [econstructor; eauto|idtac]
  end.

Lemma E_App_intro :
  forall (G : context) (b : tm) (a B A C : tm),
       Typing G q_R b (a_Pi q_R A B) -> (open_tm_wrt_tm B a) = C ->
       Typing G q_R a A -> Typing G q_R (a_App b q_R a) C.
Proof.
  intros. subst.  eapply E_App; eauto. autorewrite with l1_lattice. assumption. solve_lattice.
Qed.

Lemma E_IApp_intro :
  forall (G : context) (b : tm) (a B A C : tm),
       Typing G q_R b (a_Pi q_C A B) -> (open_tm_wrt_tm B a) = C ->
       Typing G q_C a A -> Typing G q_R (a_App b q_C a) C.
Proof.
  intros. subst.  eapply E_App; eauto. autorewrite with l1_lattice. assumption. solve_lattice.
Qed.


Lemma FixTy_erase :
  Typing nil q_C (erase_tm FixTy) a_Star.
Proof.
  use_binder E_Pi X.
  use_binder E_Pi Z.
  use_binder E_Pi W.
      (* all : try solve [best ctrs:Ctx , Typing db: l1_lattice, lattice_props]. *)
  all : try solve [qauto l: on ctrs: Ctx, Typing db: l1_lattice, lattice_props].
  hauto q: on ctrs: Ctx, Typing db: l1_lattice, lattice_props.
  use_binder E_Pi W.
  all : try solve [hauto q: on ctrs: Ctx, Typing db: l1_lattice, lattice_props].
Qed.

Lemma FixDef_FixTy_erase :
  Typing nil q_R (erase_tm FixDef) (erase_tm FixTy).
Proof.
  pose (H := AxFix). clearbody H.
  unfold FixDef,FixTy; simpl.
  use_binder E_Abs X.
  use_binder E_Abs x.
  { use_binder E_Pi Z.
    all : try solve [best ctrs:Ctx , Typing db: l1_lattice, lattice_props]. }
  { eapply E_App_intro. 
    qauto l: on ctrs: Ctx, Typing db: l1_lattice, lattice_props.
    sfirstorder ctrs: Ctx, Typing db: l1_lattice, lattice_props.
    { eapply E_App_intro; simpl.
      3 : qauto l: on ctrs: Ctx, Typing db: l1_lattice, lattice_props.
      { eapply E_IApp_intro with (a := (a_Var_f X)); simpl; eauto.
        Check E_Fam.
        autorewrite with l1_lattice in *.
        pose proof (K := @E_Fam _ q_R Fix  (erase_tm FixTy) q_R (erase_tm FixDef) ltac:(solve_lattice) H1).
        unfold toplevel, erase_sig in K.
        apply binds_map with (f:=(fun '(psi, s) => (psi, erase_csort s))) in H.
        apply K in H.
        clear K.
        simpl in H.
        apply H.
        apply FixTy_erase.
        { unfold open_tm_wrt_tm. simpl. eauto. }
        qauto l: on ctrs: Ctx, Typing db: l1_lattice, lattice_props.
      }
      unfold open_tm_wrt_tm. simpl. eauto.
    }
  }
  use_binder E_Pi Z; eauto.
  all : try solve [best ctrs:Ctx , Typing db: l1_lattice, lattice_props].
Qed.


Lemma Sig_toplevel: Sig toplevel.
Proof.
  (* best ctrs: Sig use: FixTy_erase, FixDef_FixTy_erase. *)
  qauto l: on ctrs: Sig use: FixTy_erase, FixDef_FixTy_erase.
Qed.

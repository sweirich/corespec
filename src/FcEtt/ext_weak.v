Require Import FcEtt.sigs.
Require Export FcEtt.ett_ind.
Require Import FcEtt.tactics.
Require Import FcEtt.utils.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_par.



Module ext_weak (wf: ext_wf_sig).

Include wf.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* ------------------------------------------------------------------- *)
(* Weakening Lemmas for the available set *)

(* Can replace set with an equivalent *)
Lemma respects_atoms_eq_mutual :
  (forall G r a A,     Typing G r a A       -> True) /\
  (forall G r phi,     PropWff G r phi       -> True) /\
  (forall G D r p1 p2, Iso G D r p1 p2 -> forall D', D [=] D' -> Iso G D' r p1 p2) /\
  (forall G D r A B T,   DefEq G D r A B T  -> forall D', D [=] D' -> DefEq G D' r A B T) /\
  (forall G,           Ctx G           -> True).
Proof. 
  ext_induction CON; intros; subst; eauto 2.
  all: try solve [eapply CON; eauto 2; try fsetdec].

  (* these are hard to find. *)
  (*
  eapply E_LeftRel with (b:=b)(b':=b'); eauto 2.
  eapply E_LeftIrrel with (b:=b)(b':=b'); eauto 2.
  eapply E_Right with (a:=a)(a':=a'); eauto 2.
  *)
Qed.

Definition Iso_respects_atoms_eq   := third  respects_atoms_eq_mutual.
Definition DefEq_respects_atoms_eq := fourth respects_atoms_eq_mutual.

Instance Iso_atoms_eq_mor : Morphisms.Proper
                                 (eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> iff)
                                 Iso.
Proof.
  simpl_relation; split=> ?;
  eauto using Iso_respects_atoms_eq, AtomSetProperties.equal_sym.
Qed.

Instance DefEq_atoms_eq_mor : Morphisms.Proper
                                   (eq ==> AtomSetImpl.Equal ==> eq ==> eq ==> eq ==> eq ==> iff)
                                   DefEq.
Proof.
  simpl_relation; split=> ?;
  eauto using DefEq_respects_atoms_eq, AtomSetProperties.equal_sym.
Qed.


(* ----- *)

Ltac binds_cons :=
  let H5 := fresh in
  match goal with
    [
      H4 : (∃ phi : constraint, binds ?x (Co phi) ?G) → False
      |- ((exists phi, binds ?x (Co phi) ([(?y, ?s)] ++ ?G)) -> False) ] =>
    intro H5; destruct H5; apply H4; simpl in H5;
    destruct (binds_cons_1 _ x y _ s G H5); split_hyp; subst;
    try done; eauto
  end.


Lemma strengthen_available_noncovar:
  (forall G1 r a A,    Typing G1 r a A -> True) /\
  (forall G1 r phi,    PropWff G1 r phi -> True) /\
  (forall G1 D r p1 p2, Iso G1 D r p1 p2 -> forall x, not (exists phi, binds x (Co phi) G1) ->
                 Iso G1 (remove x D) r p1 p2) /\
  (forall G1 D r A B A1,DefEq G1 D r A B A1 ->  forall x, not (exists phi, binds x (Co phi) G1) ->
                 DefEq G1 (remove x D) r A B A1) /\
  (forall G1 ,        Ctx G1 -> True).
Proof.
  eapply typing_wff_iso_defeq_mutual; eauto 3; try done.
  all: intros; unfold not in *. 
  all: try 
         match goal with [ |- DefEq _ _ _ (a_UAbs ?rho _) (a_UAbs _ _) _ ] => destruct rho end.
  all: try (E_pick_fresh y; eauto 3).
  all: try solve [destruct (x == c); [ subst; assert False; eauto | eauto]].
  all: try (eapply H0; auto; binds_cons).
  all: try (eapply H; auto; binds_cons).
  all: try (move: H5 => /binds_cons_iff [[? [?]] | /= H5]; subst;
                       assert (y <> y); [fsetdec|done|fsetdec|done]).
  all: eauto 4.
  - move: H2 => /binds_cons_iff [[? [?]] | /= H2]; subst;
                       assert (y <> y); [fsetdec|done|fsetdec|done].
Qed.  (* strengthen_available_nocovar *)

Lemma DefEq_strengthen_available_tmvar :
  forall G D r g A B, DefEq G D r g A B ->  forall x r1 A', binds x (Tm r1 A') G ->
                    forall D', D' [=] remove x D ->
                    DefEq G D' r g A B.
Proof.
  intros. eapply respects_atoms_eq_mutual.
  eapply (fourth strengthen_available_noncovar). eauto.
  unfold not.
  intros b. destruct b as [phi b].
  assert (Tm r1 A' = Co phi). eapply binds_unique; eauto.
  inversion H2.
  fsetdec.
Unshelve. exact Rel.
Qed.

(* ----- *)

Lemma weaken_available_mutual:
  (forall G1 r a A, Typing G1 r a A -> True) /\
  (forall G1 r phi,   PropWff G1 r phi -> True) /\
  (forall G1 D r p1 p2, Iso G1 D r p1 p2 -> forall D', D [<=] D' -> Iso G1 D' r p1 p2) /\
  (forall G1 D r A B T,   DefEq G1 D r A B T -> forall D', D [<=] D' -> DefEq G1 D' r A B T) /\
  (forall G1 ,       Ctx G1 -> True).
Proof.
  ext_induction CON.
  all: try done.
  all: intros; try solve [eapply CON; eauto 2].
  (*
  - eapply E_LeftRel   with (b := b) (b' := b'); eauto 2.
  - eapply E_LeftIrrel with (b:=b) (b' := b'); eauto 2.
  - eapply E_Right     with (a:=a)(a':=a'); eauto 2.
  *)
Qed.

Lemma remove_available_mutual:
  (forall G1 r a A,   Typing G1 r a A -> True) /\
  (forall G1 r phi,   PropWff G1 r phi -> True) /\
  (forall G1 D r p1 p2, Iso G1 D r p1 p2 ->
                   Iso G1 (AtomSetImpl.inter D (dom G1)) r p1 p2) /\
  (forall G1 D r A B T,   DefEq G1 D r A B T ->
                   DefEq G1 (AtomSetImpl.inter D (dom G1)) r A B T) /\
  (forall G1 ,       Ctx G1 -> True).
Proof.
  ext_induction CON.
  all: try done.
  all: eauto 2.
  all: intros. 
  all: try solve [eapply CON; eauto 2].
  (* only binding constructors left *)
  
  all: eapply (CON (L \u dom G \u D)); first auto.
  all: try intros y Fr.
  all: try eapply (fourth respects_atoms_eq_mutual).
  all: try match goal with [H0 : forall x, x `notin` ?L -> 
        DefEq _ (AtomSetImpl.inter _ _) _ _ _ _ |- _ ] => eapply H0 end; auto.
  all: simpl; fsetdec.
Qed.


Instance Iso_atoms_sub_mor : Morphisms.Proper
                                    (eq ==> AtomSetImpl.Subset ==> eq ==> eq ==> eq ==> impl)
                                    Iso.
Proof.
  simpl_relation; eapply (third weaken_available_mutual); eassumption.
Qed.

Instance DefEq_atoms_sub_mor : Morphisms.Proper
                                    (eq ==> AtomSetImpl.Subset ==> eq ==> eq ==> eq ==> eq ==> impl)
                                    DefEq.
Proof.
  simpl_relation; eapply (fourth weaken_available_mutual); eassumption.
Qed.


Lemma DefEq_weaken_available :
  forall G D r A B T, DefEq G D r A B T -> DefEq G (dom G) r A B T.
Proof.
  intros.
  remember (AtomSetImpl.inter D (dom G)) as D'.
  eapply (fourth weaken_available_mutual).
  eapply (fourth remove_available_mutual).
  eauto. subst. fsetdec.
Qed.

Lemma Iso_weaken_available :
  forall G D r A B, Iso G D r A B -> Iso G (dom G) r A B.
Proof.
  intros G D. intros.
  remember (AtomSetImpl.inter D (dom G)) as D'.
  eapply (third weaken_available_mutual).
  eapply (third remove_available_mutual).
  eauto. subst. fsetdec.
Qed.

Hint Resolve DefEq_weaken_available Iso_weaken_available : core.

Lemma binds_Co_SubG : forall G G2 x A, SubG G G2  -> binds x (Co A) G -> 
                                 binds x (Co A) G2.
Proof.
  induction 1; intros h.
  inversion h.
  destruct (binds_cons_1 _ _ _ _ _ _ h). 
  destruct H2. inversion H3. auto.
  destruct (binds_cons_1 _ _ _ _ _ _ h). 
  destruct H1 as [e1 e2]. inversion e2. subst. auto.
  auto.
Qed.

Lemma SubG_mutual :
  (forall G0 r a A, Typing G0 r a A -> forall G2, SubG G0 G2 -> Typing G2 r a A) /\
  (forall G0 r phi,   PropWff G0 r phi -> forall G2, SubG G0 G2 -> PropWff G2 r phi) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 -> forall G2, SubG G0 G2 -> Iso G2 D r p1 p2) /\
  (forall G0 D r A B T,   DefEq G0 D r A B T -> forall G2, SubG G0 G2 -> DefEq G2 D r A B T) /\
  (forall G0, Ctx G0 -> forall G2, SubG G0 G2 -> Ctx G2).
Proof. 
  ext_induction CON.
  all: intros.
  all: try solve [eapply CON; eauto 2 using binds_Co_SubG].
  all: try solve [edestruct binds_SubG as [rho3 [h0 h1]]; eauto 2;
                  eapply E_Var; eauto; eapply SubRho_trans; eauto].

  all: try solve [pick fresh x and apply CON; autofresh_fixed x; 
                  eauto 4 using PropWff_lc with lc].
  all: try solve [eapply CON; eauto 2; rewrite <- dom_SubG; eauto].
  all: try match goal with [ H : SubG ?G1 ?G2 |- _ ] => inversion H; subst; clear H end.
  all: eauto 2.
  all: econstructor; eauto;  rewrite <- dom_SubG; eauto.
Qed.

Definition Typing_SubG := first SubG_mutual.
Definition PropWff_SubG := second SubG_mutual.
Definition Iso_SubG := third SubG_mutual.
Definition DefEq_SubG := fourth SubG_mutual.

Lemma SubRho_mutual :
  (forall G r a A, Typing G r a A -> forall r2, SubRho r2 r -> Typing G r2 a A) /\
  (forall G r phi,   PropWff G r phi -> forall r2, SubRho r2 r -> PropWff G r2 phi) /\
  (forall G D r p1 p2, Iso G D r p1 p2 -> forall r2, SubRho r2 r -> Iso G D r2 p1 p2) /\
  (forall G D r A B T,   DefEq G D r A B T -> forall r2, SubRho r2 r -> DefEq G D r2 A B T) /\
  (forall G, Ctx G -> True).
Proof. 
  ext_induction CON.
  all: intros.
  all: auto.
  all: try match goal with [ H : SubRho ?r Irrel |- _ ] => inversion H; subst; clear H end.
  all: try solve [eapply CON; eauto 2].
  all: try solve [eapply E_Var; eauto using SubRho_trans]. 
  
  all: try solve [pick fresh x and apply CON; autofresh_fixed x;
                  eauto 3 using SubRho_trans].
Qed.

Definition Typing_SubRho := first SubRho_mutual.
Definition PropWff_SubRho := second SubRho_mutual.
Definition Iso_SubRho := third SubRho_mutual.
Definition DefEq_SubRho := fourth SubRho_mutual.

Corollary Typing_Irrel : forall G r a A, Typing G r a A -> Typing G Irrel a A.
Proof. eauto using Typing_SubRho. Qed.
Corollary PropWff_Irrel : forall G r phi, PropWff G r phi -> PropWff G Irrel phi.
Proof. eauto using PropWff_SubRho. Qed.

Lemma typing_weakening_mutual:
  (forall G0 r a A,     Typing G0 r a A ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Typing (F ++ E ++ G) r a A) /\
  (forall G0 r phi,     PropWff G0 r phi ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> PropWff (F ++ E ++ G) r phi) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Iso (F ++ E ++ G) D r p1 p2) /\
  (forall G0 D r A B T, DefEq G0 D r A B T ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> DefEq (F ++ E ++ G) D r A B T) /\
  (forall G0,         Ctx G0 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Ctx (F ++ E ++ G)).
Proof.
  ext_induction CON.
  all: intros; subst; try done.

  (* TODO: move E_LeftRel etc. first using ensure_case *)

  all: try solve [eapply CON; eauto 2].
  all: try solve [eapply CON; eauto 2; eapply DefEq_weaken_available; eauto 2]. 
  all: try
    match  goal with [ |- DefEq _ _ _ (a_UAbs ?rho _) (a_UAbs _ _) _] => destruct rho end.

  all: try solve [E_pick_fresh y; 
                  try auto_rew_env; apply_first_hyp; try simpl_env; eauto 3].
  all: try solve [pick fresh y and apply CON; autofresh_fixed y; eauto 3;
      auto_rew_env; eapply H; simpl_env; eauto 4 using Typing_Irrel, PropWff_Irrel]. 

  all: pick fresh y and apply CON; autofresh_fixed y; eauto 3;
  auto_rew_env;
  match goal with 
     [H0: forall E F G, _ -> Ctx _ -> DefEq _ _ _ _ _ _ |- DefEq _ _ _ _ _ _ ] => eapply H0 end;
  simpl_env; eauto 2;
  econstructor; eauto using Typing_Irrel, PropWff_Irrel.

  (*
  eapply E_LeftRel with (b:=b)(b':=b'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  eapply E_LeftIrrel with (b:=b)(b':=b'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  eapply E_Right with (a:=a)(a':=a'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  *)
Qed.


Definition Typing_weakening  := first  typing_weakening_mutual.
Definition PropWff_weakening := second typing_weakening_mutual.
Definition Iso_weakening     := third  typing_weakening_mutual.
Definition DefEq_weakening   := fourth typing_weakening_mutual.
Definition Ctx_weakening     := fifth  typing_weakening_mutual.

Fixpoint Irrel := map
  (fun b => match b with 
         | (Tm _ A) => Tm Irrel A
         | _ => b 
         end)

Lemma plus_irrelevance_mutual : 
  (forall G r a A, Typing G r a A -> r = Irrel -> Typing G r2 a A) /\
  (forall G r phi,   PropWff G r phi -> forall r2, SubRho r2 r -> PropWff G r2 phi) /\
  (forall G D r p1 p2, Iso G D r p1 p2 -> forall r2, SubRho r2 r -> Iso G D r2 p1 p2) /\
  (forall G D r A B T,   DefEq G D r A B T -> forall r2, SubRho r2 r -> DefEq G D r2 A B T) /\
  (forall G, Ctx G -> True).
Proof. 
  ext_induction CON.
  all: intros.
  all: auto.
  all: try match goal with [ H : SubRho ?r Irrel |- _ ] => inversion H; subst; clear H end.
  all: try solve [eapply CON; eauto 2].
  all: try solve [eapply E_Var; eauto using SubRho_trans]. 
  
  all: try solve [pick fresh x and apply CON; autofresh_fixed x;
                  eauto 3 using SubRho_trans].
Qed.

End ext_weak.

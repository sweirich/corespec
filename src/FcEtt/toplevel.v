Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Import FcEtt.utils.

Require Export FcEtt.fix_typing.


(* --------------------------------------------------- *)

Lemma uniq_an_toplevel : uniq an_toplevel.
Proof.
 induction AnnSig_an_toplevel; auto.
Qed.
Lemma uniq_toplevel : uniq toplevel.
Proof.
  induction Sig_toplevel; auto.
Qed.


(* ------------------------------------------ *)

(* Tactics for working with 'binds' assumptions in the context. *)
Ltac binds_case :=
  intros;
  match goal with
  | [ H : binds ?F ?s nil |- _ ] => inversion H
  | [ H : binds ?F ?s ?G |- _  ] => inversion H;
    [ (* bound here *)
      match goal with [ H3 : (_,_) = (_,_) |- _ ] => inversion H3;
      subst; try split; eauto end
    | (* bound elsewhere *)
      eauto]
  end.

Lemma toplevel_closed : forall F a A, binds F (Ax a A) toplevel -> Typing nil a A.
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  all: binds_case.
Qed.

(*
Lemma toplevel_to_const : forall T A, binds T (Cs A) toplevel -> Typing nil A a_Star.
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  all: binds_case IHst.
Qed.
*)

Lemma toplevel_to_const :
  forall K A a, binds K (Cs A a) toplevel ->
           Typing nil A a_Star /\ exists B, DataTy A B /\ Constr B.
Proof.
  have st: Sig toplevel by apply Sig_toplevel.
  induction st.
  all: binds_case.
Qed.



Lemma an_toplevel_closed : forall F a A, binds F (Ax a A) an_toplevel ->
                                    AnnTyping nil a A.
Proof.
  have st: AnnSig an_toplevel by apply AnnSig_an_toplevel.
  induction st.
  all: binds_case.
Qed.

(*
Lemma an_toplevel_to_const : forall T A, binds T (Cs A) an_toplevel ->
                                    AnnTyping nil A a_Star.
Proof.
  have st: AnnSig an_toplevel by apply AnnSig_an_toplevel.
  induction st.
  all: binds_case.
Qed.
*)
(*
Lemma binds_to_type : forall T A, binds T (Cs A) an_toplevel -> DataTy A a_Star.
Proof.
  have st: AnnSig an_toplevel by apply AnnSig_an_toplevel.
  induction st.
  all: binds_case.
Qed.
*)

Lemma an_toplevel_to_const :
  forall K A a, binds K (Cs A a) an_toplevel ->
           AnnTyping nil A a_Star /\ exists B, DataTy A B /\ Constr B.
Proof.
  have st: AnnSig an_toplevel by apply AnnSig_an_toplevel.
  induction st.
  all: binds_case.
Qed.

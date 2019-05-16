(* "Extended" computation tactics *)

(* This file provides tactics (just one, at the moment) that can reduce terms
   beyond what normal reduction can. The difference is that they can interleave
   some rewriting steps with actual reduction steps. Said rewritings  are
   specified as rewrite hints for autorewrite, in the database extended_comp.

   This is useful for functions of multiple arguments which:
   - are applied to at least one abstract argument, and thus can't normally
     reduce
   - result is easily expressible in terms of the input, once at least one
     argument is known
   This applies in particular to numerous functions performing nested pattern
   matching.

   For instance, using this, we can "reduce" `app l nil` to just `l`, instead of
   being stuck.

   Users are welcome to extend this database (extended_comp) to suit their needs.
*)

Require Import FcEtt.imports.
Require Import FcEtt.notations.

Require Export FcEtt.utils_fun.

Generalizable All Variables.


(******* Tactics *******)

Ltac ecbn :=
  cbn;
  repeat progress (autorewrite with extended_comp; cbn).

Tactic Notation "ecbn" "in" ident(H) := (move: H; ecbn; move=> H).





(******* Stock lemmas ********)


(* Lists *)

Hint Rewrite rev_app_distr app_nil_r dom_app : extended_comp.

Lemma zip_nil_r : `(@zip a b l nil = nil).
Proof. move => ?? l; by case l. Qed.

Hint Rewrite zip_nil_r : extended_comp.



(* Finite set facts *)

Lemma union_empty_r : `{
  s ∪ empty [=] s
}.
Proof. fsetdec. Qed.

Hint Rewrite @union_empty_r.

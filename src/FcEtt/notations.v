Require Export Coq.Unicode.Utf8.

Require Export FcEtt.ett_ott.
Require Export Metalib.Metatheory.

(* TODO: Modularize, so we can import on demand *)
(* Typing *)
Notation "Γ ⊨ a : A"                := (Typing Γ a A)      (at level 72, a at level 35, A at level 35)  : type_scope.
Notation "Γ ∥ Δ ⊨ a₁ ∼ a₂ : A / R" := (DefEq Γ Δ a₁ a₂ A R) (at level 72, Δ at level 35, a₁ at level 35, a₂ at level 35, A at level 35, R at level 35) : type_scope.
Notation "Γ ∥ Δ ⊨ φ₁ ∼ φ₂"         := (Iso Γ Δ φ₁ φ₂)       (at level 72, Δ at level 35, φ₁ at level 35, φ₂ at level 35): type_scope.
Notation "Γ ⊨ φ 'Ok'"               := (PropWff Γ φ)         (at level 80, φ at level 35)                 : type_scope.


(* Reductions *)
Notation "Γ ∥ D ∥ ζ ⊨ a ⇒ b / R" := (Par Γ D ζ a b R) (at level 80, b at level 35).
Notation "⊨ a ↝ b / R"  := (reduction_in_one a b R) (at level 80, b at level 35).

(* Predicates *)
(* Notation "ζ ⊨ 👻 a / R" := (roleing_tm ζ a R) (at level 80, a at level 35). *)
Notation "ζ ⊨r a : R" := (roleing ζ a R) (at level 80, a at level 35, R at level 35).


(* Other relations *)
Notation "x ∈ S" := (x `in`    S) (at level 70).
Notation "x ∉ S" := (x `notin` S) (at level 70).

Notation "s1 ⊂ s2" := (s1 [<=] s2) (at level 70).

Notation "( ρ = +)∨( x ∉ '𝕗𝕧' A )" := (RhoCheck ρ x A) (at level 70, only printing).
Notation "ρ-check ρ x A" := (RhoCheck ρ x A) (at level 70, only printing).

(* Functions *)
(* Change to ℱ𝒱 instead ?*)
Notation "'ℱν' a" := (fv_tm_tm_tm a) (at level 50, only printing).
Notation "'ℱν' a" := (fv_tm_tm_co a) (at level 50, only printing).
Notation "'ℱν' φ" := (fv_co_co_co φ) (at level 50, only printing).
Notation "'ℱν' φ" := (fv_co_co_tm φ) (at level 50, only printing).

Notation "a ∪ b" := (a `union` b) (at level 50).
Notation "a ∩ b" := (AtomSetImpl.inter a b) (at level 50).

(* Elements *)
Notation "∅" := nil.

Notation "x ⟹ y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

(* TODO: add the missing ones *)

(* FIXME: Wrong priorities. For instance, the following formula shouldn't be printed with parens:
  (G ⊨ A : T / R) ∧ G ⊨ B : T / R
*)

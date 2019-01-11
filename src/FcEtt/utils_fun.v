Require Import FcEtt.imports.

(* Simple auxiliary functions *)

Definition zip : `{list A → list B → list (A * B)} := 
  fix zip _ _ a b := 
    match a, b with
      | nil, _ => nil
      | _, nil => nil
      | x :: xs, y :: ys => (x, y) :: zip _ _ xs ys
    end.


Fixpoint map_r {A B C} f (l : list (A * B)) : list (A * C):=
  match l with
    | [] => []
    | (h1, h2) :: tl => (h1, f h2) :: map_r f tl
  end.

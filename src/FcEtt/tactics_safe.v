(* Tactics that are somehow broken by ssreflect *)




(*******************************)
(**** Basic Building Blocks ****)
(*******************************)
Ltac only_one_goal :=
  let n:= numgoals in guard n=1.
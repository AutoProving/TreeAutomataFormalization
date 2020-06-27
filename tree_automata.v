Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect (*all_algebra order*).
Set Warnings "+notation-overridden".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*   This library is heavily based upon the mathcomp.ssreflect.seq library:    *)
(*     https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html         *)
(*                                                                             *)
(*                                                                             *)
(*   Here are short descriptions of currently implemented functionality.       *)
(*   Let (r : nat), (j : [r]), (p, q, s : seq [r]), and (U, S : seq (seq [r])).*)
(*                                                                             *)
(*            [n] == the natural numbers smaller than n (aka the ordinal n)    *)
(*        seq [n] == the type of finite strings (sequences) over [n]           *)
(*  seq (seq [n]) == the type of collections of finite strings over [n]        *)
(*           [::] == the empty string (sequence)                               *)
(*         j :: p == a string corresponding to prepending the number j to the  *)
(*                   string p                                                  *)
(* [:: j1; ...; jn] == the string with the elements j1 to jn                   *)
(*       parent p == the string p without the first element                    *)
(* suffix_closed U == every sufix of an element of U is also an element of U   *)
(* well_numbered_single U (j :: p) == all the children of p with id smaller    *)
(*                                    than j are in U                          *)
(* well_numbered U == all the strings p in U are well_numbered_single U p      *)
(*                                                                             *)
(*     tree_like U == both suffix_closed and well_numbered                     *)
(*   is_parent p q == p is the parent of q                                     *)
(*    is_child p q == p is a child of q                                        *)
(*     ancestors p == the parent of p, and the parent of the parent of p, and  *)
(*                    so on                                                    *)
(*     connected S == there is only one string in S without its parent in S    *)




(*   Unlike in the paper specification, here [n] is the finite set of numbers  *)
(* between 0 and n-1, or in other words, the natural numbers i such that i < n.*)
Notation "[ n ]" := 'I_n (at level 0).


Section SuffixClosed.

Variable r : nat.

Definition parent (p : seq [r]) : seq [r] := drop 1 p.

(*   We define sufix_closed instead of prefix_closed because it is trivial     *)
(* ie, takes constant time) to drop the first element of a string but not the  *)
(* last. Thus throughout this development our strings are the reversed version *)
(* of what appears in the paper specification.                                 *)
Definition suffix_closed (U : seq (seq [r])) : bool :=
  all (fun s => parent s \in U) U.

Lemma suffix_closedP (U : seq (seq [r])) :
  reflect
    (forall (p : seq [r]) (j : [r]), j :: p \in U -> p \in U)
    (suffix_closed U).
Proof.
  apply: (iffP idP).
Admitted.

Lemma suffix_closed_correct (U : seq (seq [r])) (p : seq [r]) (n : nat) :
  suffix_closed U -> p \in U -> drop n p \in U.
Proof.
  elim: n.
Admitted.

Lemma suffix_closed_nil (U : seq (seq [r])) :
  suffix_closed U -> U != [::] -> [::] \in U.
Proof.
  case: U => [// | s U closedsU _].
  rewrite -(drop_size s).
  by apply: suffix_closed_correct => //; rewrite in_cons eqxx.
Qed.

(* TODO This doesn't look like the most efficient implementation, because it verifies every i in [r] instead of directly in [j]. This is because I didn't figure out the coersion, I'll think about it later. *)
Definition well_numbered_single (U : seq (seq [r])) (s : seq [r]) : bool :=
  match s with
  | [::] => true
  | j :: p => [forall i in [r], (i < j) ==> (i :: p \in U)]
  end.

Definition well_numbered (U : seq (seq [r])) : bool :=
  all (well_numbered_single U) U.

End SuffixClosed.


Section TreeLike.

Variable r : nat.

Definition tree_like (U : seq (seq [r])) : bool :=
  suffix_closed U && well_numbered U.

(* p is a parent of q *)
Definition is_parent (p q : seq [r]) : bool := parent p == q.

(* p is a child of q *)
Definition is_child (p q : seq [r]) : bool := is_parent q p.

(* TODO Should the empty string be an ancestor? I guess so. *)
Definition ancestors (s : seq [r]) : seq (seq [r]) :=
  [seq drop i s | i <- iota 0 (size s).+1].

Lemma self_ancestor (s : seq [r]) : s \in ancestors s.
Proof.
  rewrite /ancestors.
  set f := drop^~ s; have -> : s = f 0 by rewrite /f drop0.
  by apply: map_f.
Qed.

Lemma suffix_closed_ancestors (U : seq (seq [r])) (p : seq [r]) :
  suffix_closed U -> p \in U -> all (mem U) (ancestors p).
Proof.
  move=> scU pinU; rewrite /ancestors.
  apply /allP => j /mapP[n _] ->.
  by apply: suffix_closed_correct.
Qed.

(* TODO descendants *)
(* TODO leaves *)
(* TODO all_leaves *)

(* TODO maybe the empty S should also be connected *)
Definition connected (S : seq (seq [r])) : bool :=
  count (fun p => (p == [::]) || ((p != [::]) && (parent p \notin S))) S == 1.

End TreeLike.


(* Examples and tests *)
Notation "'z" := (@Ordinal 2 0 isT) (at level 0).
Notation "'o" := (@Ordinal 2 1 isT) (at level 0).
Eval cbv in well_numbered [:: [:: 'z]]. (* why? :( *)
Eval cbv in map (fun x => map val x) (ancestors [:: 'o; 'z; 'o]).

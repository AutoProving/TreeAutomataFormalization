Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Warnings "+notation-overridden".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*   This library is heavily based upon the mathcomp.ssreflect.seq library:    *)
(*     https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html         *)
(*                                                                             *)
(*                                                                             *)
(*   Here are short descriptions of currently implemented functionality.       *)
(*   Let (r j k : nat), (p, q, s : string), and (U, S : prototree).           *)
(*                                                                             *)
(*                                 DATATYPES                                   *)
(*              nat == the natural numbers                                     *)
(*              [r] == the natural numbers smaller than r (aka the ordinal r)  *)
(*           string == the type of finite strings (sequences) over the natural *)
(*                     numbers                                                 *)
(*       prototree == the type of lists of finite strings over nat            *)
(*             [::] == the empty list (or string depending on its type)        *)
(*           j :: p == a string corresponding to prepending the number j to    *)
(*                     the string p                                            *)
(* [:: j1; ...; jn] == the string with the elements j1 to jn                   *)
(*                                                                             *)
(*                              SUFFIX-CLOSED                                  *)
(*         parent p == the string p without the first element, or [::] if p is *)
(*                     empty                                                   *)
(*  suffix_closed U == every sufix of an element of U is also an element of U  *)
(*  well_numbered U == if (j :: p) is in U, then for every k <= j, the string  *)
(*                     (k :: p) is also in U                                   *)
(*                                                                             *)
(*                                TREE-LIKE                                    *)
(*      tree_like U == suffix-closed, well-numbered and without duplicates     *)
(*    is_parent p q == p is the parent (i.e. the first suffix) of q            *)
(*     is_child p q == q is the parent of p                                    *)
(*  is_ancestor p q == p is a suffix of q                                      *)
(*      ancestors p == every suffix of p                                       *)
(* is_strict_ancestor p q == p is a suffix of q, but p is not q                *)
(*     children U p == a list of all the children of p in U                    *)
(*  descendants U p == a list of all the children of p, and the children of the*)
(*                     children, and so on, as long as they are in U           *)
(*      is_leaf U p == there are no descendants of p in U                      *)
(*         leaves U == a list of all the leaves of U                           *)
(*      connected S == there is only one string in S without its parent in S   *)




(*   Unlike in the paper specification, here [r] is the finite set of numbers  *)
(* between 0 and r-1, or in other words, the natural numbers i such that i < r.*)
Notation "[ r ]" := 'I_r (at level 0).

(*   There is an implicit coercion nat_of_ord : [r] -> nat that allows         *)
(* functions on nat to seamleslly recieve inputs of type [r].                  *)

(*   For now we define everything over the natural numbers instad of [r]       *)
(* because it is better to compute with "raw" data types, i.e. datatypes       *)
(* without proofs. As soon as this restriction is necessary we can add it and  *)
(* make use of the coersion from nat to [r] to use the following definitions.  *)


(*   We use lists of natural numbers to represent strings.                     *)
Definition string := seq nat.

Definition bstring (r : nat) := seq [r].
Notation "[ r *]" := (bstring r) (at level 0).

Coercion string_of_bstring (r : nat) : [r*] -> string := map val.

Definition prototree := seq string.

Definition bprototree (r : nat) := seq [r*].

Coercion prototree_of_bprototree (r : nat) : bprototree r -> prototree :=
  map (@string_of_bstring r).

Definition parent (p : string) : string := drop 1 p.

Lemma parent_cons (p : string) (j : nat) : parent (j :: p) = p.
Proof. by rewrite /parent /= drop0. Qed.
Hint Resolve parent_cons : core.

Lemma parent_nil : parent [::] = [::].
Proof. by []. Qed.
Hint Resolve parent_nil : core.

(*   We define sufix_closed instead of prefix_closed because it is trivial     *)
(* (ie, takes constant time) to drop the first element of a string but not the *)
(* last. Thus throughout this development our strings are the reversed version *)
(* of what appears in the paper specification.                                 *)
Definition suffix_closed (U : prototree) : bool :=
  all (fun s => parent s \in U) U.

Lemma suffix_closedP (U : prototree) :
  reflect
    (forall (p : string) (j : nat), j :: p \in U -> p \in U)
    (suffix_closed U).
Proof.
  rewrite /suffix_closed.
  apply: (iffP idP).
    move=> /allP scU p j.
    rewrite -{2}(parent_cons p j).
    by apply: scU.
  move=> H; apply /allP; case => [// | j p].
  by rewrite parent_cons; apply: H.
Qed.

Lemma suffix_closed_correct (U : prototree) (p : string) (n : nat) :
  suffix_closed U -> p \in U -> drop n p \in U.
Proof.
  move=> /allP scU; move: p; elim: n => [p | n IH].
    by rewrite drop0.
  case => [// | j p jpinU].
  rewrite drop_cons; apply: IH.
  by rewrite -(parent_cons p j); apply: scU.
Qed.

Lemma suffix_closed_nil (U : prototree) :
  suffix_closed U -> U != [::] -> [::] \in U.
Proof.
  case: U => [// | s U closedsU _].
  rewrite -(drop_size s).
  by apply: suffix_closed_correct => //; rewrite in_cons eqxx.
Qed.

Definition well_numbered_single (U : prototree) (s : string) : bool :=
  match s with
  | [::] => true
  | j :: p => j.-1 :: p \in U
  end.

Definition well_numbered (U : prototree) : bool :=
  all (well_numbered_single U) U.

Lemma well_numberedP (U : prototree) :
  reflect
    (forall (p : string) (j : nat),
        j :: p \in U -> forall (k: nat), k <= j -> k :: p \in U)
    (well_numbered U).
Proof.
  apply: (iffP idP).
    move=> /allP; rewrite /well_numbered_single => wnU p j jpinU k kleqj.
    set i := (j - k).
    have: (k = j - i) by rewrite /i subKn.
    move=> ->.
    elim: i => [| n IH].
      by rewrite subn0.
    rewrite subnS.
    by apply: wnU _ IH.
  move=> H.
  apply /allP => p.
  case: p =>// a l alinU.
  by apply: (H _ a) => //; apply: leq_pred.
 Qed.


Definition tree_like (r : nat) (U : bprototree r) : bool :=
  suffix_closed U && well_numbered U && uniq U.

(* p is a parent of q *)
Definition is_parent (p q : string) : bool := parent p == q.

(* p is a child of q *)
Definition is_child (p q : string) : bool := is_parent q p.

Definition is_ancestor (p q : string) : bool :=
  p == drop (size q - size p) q.

Lemma is_ancestorpp p : is_ancestor p p.
Proof.
  by rewrite /is_ancestor subnn drop0.
Qed.

Definition ancestors (s : string) : seq string :=
  [seq drop i s | i <- iota 0 (size s).+1].

Lemma suffix_closed_ancestors (U : prototree) (p : string) :
  suffix_closed U -> p \in U -> all (mem U) (ancestors p).
Proof.
  move=> scU pinU; rewrite /ancestors.
  apply /allP => j /mapP[n _] ->.
  by apply: suffix_closed_correct.
Qed.

Lemma is_ancestor_ancestors (p q : string) :
  is_ancestor p q -> p \in ancestors q.
Proof.
  rewrite /is_ancestor /ancestors => /eqP ancp.
  rewrite ancp.
  suff : (size q - size p) \in (iota 0 (size q).+1) by apply: map_f.
  by rewrite mem_iota add0n ltnS leq_subr.
Qed.

Definition is_strict_ancestor (p q : string) : bool :=
  let d := (size q - size p) in
  (d != 0) && (p == drop d q).

Lemma is_strict_ancestorW (p q : string) :
  is_strict_ancestor p q -> is_ancestor p q.
Proof. by move=> /andP []. Qed.

Lemma self_ancestor (s : string) : s \in ancestors s.
Proof.
  rewrite /ancestors.
  set f := drop^~ s; have -> : s = f 0 by rewrite /f drop0.
  by apply: map_f; rewrite mem_iota.
Qed.

Definition children  (U : prototree) (p : string) : seq string :=
  [seq s <- U | is_parent p s].

Definition descendants (U : prototree) (p : string) : seq string :=
  [seq s <- U | is_ancestor p s].

Definition is_leaf (U : prototree) (s : string) :=
  all (fun p => ~~ (is_strict_ancestor s p)) U.

Definition leaves (U : prototree) : seq string :=
  [seq s <- U | is_leaf U s].

(* TODO maybe the empty S should also be connected *)
Definition connected (S : prototree) : bool :=
  count (fun p => (p == [::]) || (parent p \notin S)) S == 1.

Lemma connected_correct (S : prototree) (p : string) :
  (p == [::]) || (parent p \notin S) =
  (p == [::]) || (p != [::]) && (parent p \notin S).
Proof. by case: p. Qed.


Section Terms.

Variable r : nat.
Variable X : finType.

Definition terms := bstring r -> X.

Definition default_term (a : X) : terms :=
  fun (s : string) => a.

Definition build_term (a : X) (ts : seq terms) : terms :=
  fun (s : string) =>
    match rev s with
    | [::] => a
    | j :: p => (nth (default_term a) ts j) p
    end.

End Terms.

Definition tfst {X Y Z : Type} (d : X * Y * Z) :=
  match d with (a, b, c) => a end.
Notation "d ~1" := (tfst d) (at level 2).

Definition tscd {X Y Z : Type} (d : X * Y * Z) :=
  match d with (a, b, c) => b end.
Notation "d ~2" := (tscd d) (at level 2).

Definition thrd {X Y Z : Type} (d : X * Y * Z) :=
  match d with (a, b, c) => c end.
Notation "d ~3" := (thrd d) (at level 2).

Section TreeAutomata.

Variable X : finType.
Variable states : finType.

Record bu_tree_automata := mk_bu_tree_automata {
  final_states : seq states;
  transitions : seq (seq states * X * states);
}.

Definition automata_size (A : bu_tree_automata) : nat :=
  #|states| + size (transitions A).

(*
Definition L (A : bu_tree_automata) (q : states) (i : nat) : seq (terms X) :=
  match i with
  | 0 => [::]
  | 1 => filter (fun d => (d~1 == [::]) && (d~3 == q)) (transitions A)
  | _ => [::]
  end.
*)

(*
  match (transitions A) with
  | [::] => [::]
  | ([::], a, q) :: tl => [::]
  | (q1 :: qs, a, q) :: tl => [::]
  end.
*)

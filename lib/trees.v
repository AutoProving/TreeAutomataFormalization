Set Warnings "-notation-overridden, -notation-incompatible-format".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-format".

Require Import Coq.Program.Wf.

Require Import basic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************************)
(*   This library is heavily based upon mathcomp.ssreflect libraries such as:  *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html         *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html     *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.tuple.html       *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.finfun.html      *)
(*                                                                             *)
(*                                                                             *)
(*   Here are short descriptions of the functionality currently implemented.   *)
(*                                                                             *)
(*                                                                             *)
(*                        *** STRING-BASED TYPES ***                           *)
(*                                                                             *)
(*   Let (r : nat) (j, k : [r]) (p, q, s : [r*]) (U : ptree) (T : Type).       *)
(*                                                                             *)
(*                                 DATATYPES                                   *)
(*              nat == the natural numbers                                     *)
(*              [r] == the natural numbers smaller than r (aka the ordinal r)  *)
(*             [r*] == the type of finite strings over [r]                     *)
(*          ptree r == the type of lists of [r*]                               *)
(*             [::] == the empty list (or string depending on its type)        *)
(*           j :: p == a string corresponding to prepending j to p             *)
(* [:: j1; ...; jn] == the string with the elements j1 to jn                   *)
(*       r.-tuple T == the type of tuples with r elements of type T            *)
(*              T^r == the type of the finite functions with input [r] and     *)
(*                     output T; isomorphic to r.-tuple T, but structurally    *)
(*                     positive                                                *)
(*                                                                             *)
(*   The following coercions are available:                                    *)
(*   - From [r] to nat                                                         *)
(*   - From r.-tuple T to seq T                                                *)
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
(*      connected U == there is only one string in U without its parent in U   *)
(*                                                                             *)



(*   Unlike in the paper specification, here [r] is the finite set of numbers  *)
(* between 0 and r-1, or in other words, the natural numbers i such that i < r.*)
Notation "[ r ]" := 'I_r (at level 0, format "[ r ]").

(*   There is an implicit coercion nat_of_ord : [r] -> nat that allows         *)
(* functions on nat to seamleslly recieve inputs of type [r].                  *)


(*   We use lists of elements of [r] to represent bounded strings, or [r*].    *)
(* We use the notation [r*] instead of [r]* because there could be parsing     *)
(* mistakes by parsing [r]* as the already existing notation [r] followed by *.*)
Definition string (r : nat) := seq [r].
Notation "[ r *]" := (string r) (at level 0, format "[ r *]").

(* Pre-trees, i.e., structures that could be ill-formed trees *)
Definition ptree (r : nat) := seq [r*].

Section Strings.

Variable r : nat.

Definition parent (p : [r*]) : [r*] := drop 1 p.

Lemma parent_cons (p : [r*]) (j : [r]) : parent (j :: p) = p.
Proof. by rewrite /parent /= drop0. Qed.
Hint Resolve parent_cons : core.

Lemma parent_nil : parent [::] = [::].
Proof. by []. Qed.
Hint Resolve parent_nil : core.

(*   We define sufix_closed instead of prefix_closed because it is trivial     *)
(* (ie, takes constant time) to drop the first element of a string but not the *)
(* last. Thus throughout this development our strings are the reversed version *)
(* of what appears in the paper specification.                                 *)
Definition suffix_closed (U : ptree r) : bool :=
  all (fun s => parent s \in U) U.

Lemma suffix_closedP (U : ptree r) :
  reflect
    (forall (p : [r*]) (j : [r]), j :: p \in U -> p \in U)
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

Lemma suffix_closed_correct (U : ptree r) (p : [r*]) (n : nat) :
  suffix_closed U -> p \in U -> drop n p \in U.
Proof.
  move=> /allP scU; move: p; elim: n => [p | n IH].
    by rewrite drop0.
  case => [// | j p jpinU].
  rewrite drop_cons; apply: IH.
  by rewrite -(parent_cons p j); apply: scU.
Qed.

Lemma suffix_closed_nil (U : ptree r) :
  suffix_closed U -> U != [::] -> [::] \in U.
Proof.
  case: U => [// | s U closedsU _].
  rewrite -(drop_size s).
  by apply: suffix_closed_correct => //; rewrite in_cons eqxx.
Qed.

Definition wdord (k : [r.+1]) : [k] -> [r] :=
  @widen_ord k r (ltn_ord k).

Lemma wdord_eq (k : [r.+1]) (i j : [k]) :
  (wdord i == wdord j) = (i == j).
Proof.
  apply /idP /idP => [/eqP eqwdij | /eqP -> //].
  have /= eqij : val (wdord i) = val (wdord j) by rewrite eqwdij.
  by apply /eqP; apply: val_inj.
Qed.

Definition maxo (m n : [r]) : [r] :=
  if m < n then n else m.

Lemma maxn_maxo (m n : [r]) : maxn m n = maxo m n.
Proof. by rewrite /maxo /maxn; case: ifP. Qed.

Definition So (k : [r]) : [r.+1] := @Ordinal r.+1 k.+1 (ltn_ord k).

Lemma S_So (k : [r]) : k.+1 = So k.
Proof. by []. Qed.

Definition subon (j : [r]) (n : nat) : [r].
Proof.
  refine (@Ordinal r (j - n) _).
  by move: j => [j jltr]; rewrite (leq_ltn_trans _ jltr) ?leq_subr.
Defined.
Notation "j -on k" := (subon j k) (at level 50, format "j  -on  k").

Lemma subn_subon (j : [r]) (n : nat) : j - n = j -on n.
Proof. by []. Qed.

Definition well_numbered_single (U : ptree r) (s : [r*]) : bool :=
  match s with
  | [::] => true
  | j :: p => (j -on 1) :: p \in U
  end.

Definition well_numbered (U : ptree r) : bool :=
  all (well_numbered_single U) U.

Lemma well_numberedP (U : ptree r) :
  reflect
    (forall (p : [r*]) (j : [r]),
        j :: p \in U -> forall (k : [r]), k <= j -> k :: p \in U)
    (well_numbered U).
Proof.
  apply: (iffP idP).
    move=> /allP /=; rewrite /well_numbered_single => wnU p j jpinU k kleqj.
    set i := j - k.
    have -> : k = j -on i by apply: val_inj; rewrite /i /= subKn.
    elim: i => [| n IH].
      suff -> : j -on 0 = j => //.
      by apply: val_inj; rewrite /= subn0.
    have -> : j -on n.+1 = j -on n -on 1.
      by apply: val_inj; rewrite /= subnS subn1.
    by apply: wnU _ IH.
  move=> H; apply /allP; case => // a l alinU.
  by apply: (H _ a) => //; apply: leq_subr.
Qed.


Definition tree_like (U : ptree r) : bool :=
  [&& suffix_closed U, well_numbered U & uniq U].

Lemma tree_likeP (U : ptree r) :
  reflect
    [/\ suffix_closed U, well_numbered U & uniq U]
    (tree_like U).
Proof. by apply: (iffP and3P). Qed.

Lemma tree_like_nil (U : ptree r) :
  tree_like U -> U != [::] -> [::] \in U.
Proof.
  by move=> /tree_likeP [? _ _]; apply: suffix_closed_nil.
Qed.

(*
Record tree := Tree {
  ptree_of_tree :> ptree r;
  _ : tree_like ptree_of_tree
}.
*)

(* p is a parent of q                                                          *)
Definition is_parent (p q : [r*]) : bool := (parent q == p) && (q != [::]).

Lemma is_parentP (p q : [r*]) :
  reflect
    (exists i : [r], q = i :: p)
    (is_parent p q).
Proof.
  rewrite /is_parent /parent.
  apply: (iffP idP).
    case: q => [/andP [] //| i q /= /andP []].
    by rewrite drop0 => /eqP -> _; exists i.
  by move=> [i ->] /=; rewrite drop0 eqxx.
Qed.

Lemma is_parent_strict (p : [r*]) :
  ~ (is_parent p p).
Proof.
  move=> /is_parentP [i /eqP].
  elim: p => [// | x p IH].
  by rewrite eqseq_cons => /andP [/eqP ->].
Qed.

(* p is a child of q                                                           *)
Definition is_child (p q : [r*]) : bool := is_parent q p.

Definition is_ancestor (p q : [r*]) : bool :=
  p == drop (size q - size p) q.

Lemma is_ancestorpp p : is_ancestor p p.
Proof.
  by rewrite /is_ancestor subnn drop0.
Qed.

Definition ancestors (s : [r*]) : seq [r*] :=
  [seq drop i s | i <- iota 0 (size s).+1].

Lemma suffix_closed_ancestors (U : ptree r) (p : [r*]) :
  suffix_closed U -> p \in U -> all (mem U) (ancestors p).
Proof.
  move=> scU pinU; rewrite /ancestors.
  apply /allP => j /mapP[n _] ->.
  by apply: suffix_closed_correct.
Qed.

Lemma is_ancestor_ancestors (p q : [r*]) :
  is_ancestor p q -> p \in ancestors q.
Proof.
  rewrite /is_ancestor /ancestors => /eqP ancp.
  rewrite ancp.
  suff : (size q - size p) \in (iota 0 (size q).+1) by apply: map_f.
  by rewrite mem_iota add0n ltnS leq_subr.
Qed.

Definition is_strict_ancestor (p q : [r*]) : bool :=
  let d := (size q - size p) in
  (d != 0) && (p == drop d q).

Lemma is_strict_ancestorW (p q : [r*]) :
  is_strict_ancestor p q -> is_ancestor p q.
Proof. by move=> /andP []. Qed.

Lemma is_parent_is_strict_ancestor (p q : [r*]) :
  is_parent p q -> is_strict_ancestor p q.
Proof.
  by move=> /is_parentP [i ->]; rewrite /is_strict_ancestor subSnn /= drop0.
Qed.

Lemma self_ancestor (s : [r*]) : s \in ancestors s.
Proof.
  rewrite /ancestors.
  set f := drop^~ s; have -> : s = f 0 by rewrite /f drop0.
  by apply: map_f; rewrite mem_iota.
Qed.

Lemma is_ancestorP (U : ptree r) (p q : [r*]) :
  reflect
    (exists s : [r*], q = s ++ p)
    (is_ancestor p q).
Proof.
  apply: (iffP idP).
    move=> /eqP ->.
    exists (take (size q - size p) q).
    by rewrite cat_take_drop.
  by move=> [s ->]; rewrite /is_ancestor size_cat addnmBm drop_size_cat.
Qed.

Definition children (U : ptree r) (p : [r*]) : seq [r*] :=
  filter (is_parent p) U.

Lemma childrenP (U : ptree r) (p c : [r*]) :
  reflect
    (is_parent p c /\ c \in U)
    (c \in children U p).
Proof.
  by rewrite mem_filter; apply: (iffP andP).
Qed.

Lemma children_mem (U : ptree r) (p c : [r*]) :
  c \in children U p -> c \in U.
Proof.
  by move=> /childrenP [].
Qed.

Definition height (U : ptree r) : nat :=
  \max_(p <- U) size p.

End Strings.

Section Strings2.

Variable r : nat.

Definition arity (U : ptree r.+1) (p : [r.+1*]) : [r.+2] :=
  if children U p is [::] then ord0 else
    So (\big[@maxo r.+1/ord0]_(c <- children U p) head ord0 c).

Definition arity_nat (U : ptree r.+1) (p : [r.+1*]) : nat :=
  if children U p is [::] then 0 else
    (\max_(c <- children U p) head ord0 c).+1.

Lemma bmaxn_bmaxo (n : nat) (s : seq [n.+1*]) (F : [n.+1*] -> [n.+1]) :
  \max_(x <- s) F x = \big[@maxo n.+1/ord0]_(x <- s) F x.
Proof.
  elim: s => [| x s IH]; first by rewrite 2!big_nil.
  by rewrite 2!big_cons IH maxn_maxo.
Qed.

Lemma arity_val (U : ptree r.+1) (p : [r.+1*]) :
  arity_nat U p = arity U p.
Proof.
  rewrite /arity_nat /arity.
  case: (children U p) => [// | c cs].
  by rewrite -S_So -bmaxn_bmaxo.
Qed.

Lemma arity0 (s : [r.+1*]) :
  arity [:: [::]] s = ord0.
Proof.
  by rewrite /arity /= /is_parent /= andbF.
Qed.

Definition children_from_arity (p : [r*]) (k : [r.+1]) : k.-tuple [r*] :=
  [tuple (wdord i) :: p | i < k].

Lemma children_from_arityP  (p : [r*]) (k : [r.+1]) (c : [r*]) :
  reflect
    (exists (i : [k]), c = wdord i :: p)
    (c \in children_from_arity p k).
Proof.
  apply: (iffP idP).
    by move=> /tnthP [i]; rewrite tnth_map tnth_ord_tuple => ->; exists i.
  by move=> [i ->]; apply /tnthP; exists i; rewrite tnth_map tnth_ord_tuple.
Qed.

Lemma children_from_arity0 (p : [r*]) :
  children_from_arity p ord0 = [tuple].
Proof. by rewrite tuple0. Qed.

Definition descendants (U : ptree r) (p : [r*]) : seq [r*] :=
  filter (is_ancestor p) U.

Definition descendants_subtree (U : ptree r) (p : [r*]) : ptree r :=
  [seq take (size s - size p) s| s <- descendants U p].

Lemma descendants_uniq (U : ptree r) (p : [r*]) :
  uniq U -> uniq (descendants U p).
Proof.
  by move=> uniqU; rewrite filter_uniq.
Qed.

Lemma descendantsP (U : ptree r) (p : [r*]) (d : [r*]) :
  reflect
    (exists s : [r*], d = s ++ p /\ d \in U)
    (d \in descendants U p).
Proof.
  rewrite /descendants mem_filter.
  apply: (iffP idP).
    by move=> /andP [/(is_ancestorP U) [s seq] dinU]; exists s.
  move=> [s [deqsp ->]].
  by rewrite andbT; apply /(is_ancestorP U); exists s.
Qed.

Lemma descendants_subtree_tree_like (U : ptree r) (p : [r*]) :
    tree_like U ->
    p \in U ->
  tree_like (descendants_subtree U p).
Proof.
  move=> /and3P [scU wnU uniqU] pinU.
  apply /and3P; split.
  - admit.
  - admit.
  - rewrite map_inj_in_uniq ?descendants_uniq //.
    move=> /= d1 d2 /descendantsP [s1 [-> _]] /descendantsP [s2 [-> _]].
    by rewrite 2!size_cat 2!addnmBm 2!take_cat 2!ltnn 2!subnn take0 2!cats0 =>->.
Admitted.

Definition is_leaf (U : ptree r) (s : [r*]) :=
  all (fun p => ~~ (is_parent s p)) U.

Lemma height_is_leaf (U : ptree r) (p : [r*]) :
    size p = height U ->
  is_leaf U p.
Proof.
  rewrite /height => size_max.
  apply /allP => /= q qinU; apply /negP => parentpq.
  have /andP [szneq0 /eqP eqpdrop] := is_parent_is_strict_ancestor parentpq.
  move: szneq0; suff -> : size q - size p == 0 by [].
  by rewrite subn_eq0 size_max leq_bigmax_list.
Qed.

Lemma children_is_leaf (U : ptree r) (l : [r*]) :
  is_leaf U l = (children U l == [::]).
Proof.
  apply /idP /idP.
    move=> /allP /= lleaf; rewrite /children -(filter_pred0 U); apply /eqP.
    apply: eq_in_filter => /= p pinU; rewrite /is_parent.
    apply /andP => [[/eqP parentpisl pneqnil]].
    have := lleaf p pinU; apply /negP /negPn /andP.
    by rewrite parentpisl pneqnil.
  rewrite /children /is_leaf => childrennil; apply /all_filterP.
  rewrite -{2}(filter_predT U).
  apply: eq_in_filter => /= p pinU.
  apply /negP => parentlp; move: childrennil; apply /negP.
  rewrite -has_filter; apply /hasP => /=.
  by exists p.
Qed.

Definition leaves (U : ptree r) : seq [r*] :=
  [seq s <- U | is_leaf U s].

(* TODO maybe the empty S should also be connected *)
Definition connected (S : ptree r) : bool :=
  count (fun p => (p == [::]) || (parent p \notin S)) S == 1.

Lemma connected_correct (S : ptree r) (p : [r*]) :
  (p == [::]) || (parent p \notin S) =
  (p == [::]) || (p != [::]) && (parent p \notin S).
Proof. by case: p. Qed.

End Strings2.

Lemma arity_leaf (r : nat) (U : ptree r.+1) (l : [r.+1*]) :
  is_leaf U l -> arity U l = ord0.
Proof.
  by rewrite children_is_leaf /arity => /eqP ->.
Qed.

(*
Definition arity2 (r : nat) (U : ptree r.+1) (p : [r.+1*]) : nat :=
  if children U p is [::] then 0 else
    (\max_(c <- children U p) (head ord0 c)).+1.

Lemma arity12 (r : nat) (U : ptree r.+1) (p : [r.+1*]) :
    tree_like U ->
  arity U p = arity2 U p.
Proof.
  move=> /and3P [scU /well_numberedP wnU uniqU].
  rewrite /arity /arity2.
  set cs := children U p.
  elim: cs => [// | j s IH /=].
  congr S; rewrite IH big_cons.
Admitted.

Lemma arity_tree_like (r : nat) (U : ptree r) (p : [r*]) :
    tree_like U ->
  arity U p < r.
Proof.
Admitted.

*)

Definition children_indexes (r : nat) (U : ptree r.+1) (p : [r.+1*])
    : seq [r.+1] :=
  [seq head ord0 c | c <- children U p].

Lemma children_map (r : nat) (U : ptree r.+1) (p : [r.+1*]) :
  children U p = [seq i :: p | i <- children_indexes U p].
Proof.
Admitted.

Lemma max_in_children (r : nat) (U : ptree r.+1) (p : [r.+1*]) :
   ~ is_leaf U p ->
 (\big[@maxo r.+1/ord0]_(c <- children U p) head ord0 c) :: p \in children U p.
Proof.
  (*
  Search is_leaf.
  rewrite {2}children_map /children_indexes; apply: map_f.
  rewrite /max ischildren.
  Search (\max_(_ <- _) _) mem.
  *)
Admitted.

Lemma children_arityP (r : nat) (U : ptree r.+1) (p : [r.+1*]) :
    tree_like U ->
    p \in U ->
  perm_eq (children U p) (children_from_arity p (arity U p)).
Proof.
  move=> /tree_likeP [scU /well_numberedP wnU uniqU] pinU.
  apply: uniq_perm; first by apply: filter_uniq.
    rewrite map_inj_in_uniq ?enum_uniq //= => n m _ _ /eqP.
    by rewrite eqseq_cons wdord_eq => /andP [/eqP -> _].
  move=> /= s.
  apply /idP /idP.
    move=> /childrenP [/is_parentP [j ->] sinU].
    apply /children_from_arityP.
    (* need to show that j < arity U p *)
    eexists.
    apply /eqP; rewrite eqseq_cons eqxx andbT.
    admit.
  move=> /children_from_arityP [i ->].
  apply /childrenP; split.
    by apply /is_parentP; exists (wdord i).
  move: i; rewrite /arity.
  case ischildren : (children U p) => [| c cs]; first by move=> [].
  rewrite -ischildren.
  set max := \big[_/_]_(_ <- _) _ => i.
  apply: (wnU _ max); last by move: i => [].
  apply: (@children_mem _ _ p); rewrite max_in_children //.
  admit.
Admitted.

Lemma arity_size (r : nat) (U : ptree r.+1) (p : [r.+1*]) :
    tree_like U ->
    p \in U ->
  arity U p = size (children U p) :> nat.
Proof.
  move=> tlikeU pinU.
  rewrite (perm_size (children_arityP tlikeU pinU)).
  by rewrite /children_from_arity size_map size_enum_ord.
Qed.

Lemma mem_child (r : nat) (U : ptree r.+1) (p : [r.+1*]) (i : [arity U p]) :
  tree_like U -> p \in U -> wdord i :: p \in U.
Proof.
  move=> tlikeU pinU.
  apply: (@children_mem _ _ p).
  rewrite (perm_mem (children_arityP tlikeU pinU)).
  apply /children_from_arityP.
  by exists i.
Qed.

(*
Program Fixpoint test (r : nat) (U : ptree r.+1) (P : [r.+1*] -> Prop)
    (tlikeU : tree_like U)
    (PP : forall p, P p)
  (p : [r.+1*]) {measure (size p)} : P p :=
  match Sumbool.sumbool_of_bool (p == [::]) with
  | left leafp => PP p
  | right notleafp => PP p
  end.
Admit Obligations.
*)

Unset Program Cases.
(*Program Fixpoint*) Lemma child_ind1 (r : nat) (U : ptree r.+1) (P : [r.+1*] -> Prop)
    (tlikeU : tree_like U)
    (Pleaves : forall l : [r.+1*], l \in U ->
      is_leaf U l -> P l
    )
    (Pchildren : forall p : [r.+1*], p \in U ->
        (forall i : [arity U p], P (wdord i :: p)) ->
      P p
    )
  (p : [r.+1*]) (pinU : p \in U) (*{measure (height U - size p)}*) : P p.
Admitted.
(*
  :=
  match Sumbool.sumbool_of_bool (is_leaf U p) with
  | left leafp => Pleaves p pinU leafp
  | right notleafp =>
    Pchildren p pinU (fun i => child_ind1 tlikeU Pleaves Pchildren (mem_child i tlikeU pinU))
  end.
Next Obligation.
  apply /ltP; rewrite subnS ltn_predL subn_gt0 /height.
  rewrite ltn_neqAle; apply /andP; split; last first.
    by rewrite leq_bigmax_list.
  apply /eqP => size_max (*{Heq_anonymous}*); move: notleafp.
  move => {Pchildren child_ind1}.
  by rewrite height_is_leaf.
(* FIXME takes about 5 hours to compile *)
Qed.
*)

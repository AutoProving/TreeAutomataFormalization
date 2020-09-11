Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".

Require Import Coq.Program.Wf.

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
(*                                                                             *)
(*                           *** TREE-BASED TYPES ***                          *)
(*                                                                             *)
(*   Let (T : Type) (r i n : nat) (Sigma : finType) (t : tterm r Sigma)        *)
(* (state : finType) (q : state) (A : tbuta r Sigma state) (t' : tsterm).      *)
(*                                                                             *)
(*                                    TERMS                                    *)
(*          ttree r == structural trees with constructors                      *)
(*                     - leaf                                                  *)
(*                     - node k f                                              *)
(*                     where (k : [r.+1]) is the arity of the node (i.e., the  *)
(*                     number of children) and (f : ttree^k) is a finite       *)
(*                     function assigning a child to each (j : [k])            *)
(*    tterm r Sigma == structural terms with constructors                      *)
(*                     - tleaf a                                               *)
(*                     - tnode a k f                                           *)
(*                     where (a : Sigma) is a label, (k : [r.+1]) is the arity *)
(*                     of the node and (f : tterm^k) is as above               *)
(*       tterm_nind == a nested induction principle for tterm (the standard    *)
(*                     one is as weak as a case analysis)                      *)
(*           tpos t == the ttree obtained from t by forgeting the labels       *)
(*      positions t == the ptree corresponding to t                            *)
(*      tchildren t == a list of the children of t as tterms                   *)
(*                                                                             *)
(*                                  AUTOMATA                                   *)
(*    tbuta r Sigma state == bottom-up tree automata with the following fields *)
(*                     - (final : seq state) represents the final (i.e.,       *)
(*                       accepting) states                                     *)
(*                     - (transitions : {ffun forall k : [r.+1],               *)
(*                         seq (k.-tuple state * Sigma * state)})              *)
(*                       represents the transition function. Thus,             *)
(*                       (transitions k) is the list of the transitions with   *)
(*                       arity k                                               *)
(*      buta_size A == the size of the automaton A, equal to the sum of the    *)
(*                     number of states with the number of transitions         *)
(* reach_at_depth A q t i == in the automaton A, term t reaches state q in at  *)
(*                     most i steps                                            *)
(* reach_eventually A q t == in A, t eventually reaches q                      *)
(*      accepts A t == t eventually reaches one of the final states of A       *)
(*  transitions_preim A q == the transitions of A that have q as a consequent  *)
(*    in_degree_state A q == the number of transitions of A that have q as a   *)
(*                     consequent                                              *)
(*      in_degree A == the maximum in-degree of any given state of A           *)
(* restrict r Sigma state A n (nler : n <= r) == the (tbuta n Sigma state)     *)
(*                     automaton corresponding to A without the transitions    *)
(*                     with greater than n arity                               *)
(*                                                                             *)
(*   Let (st1 st2 : finType)  (r1 r2 : nat)                                    *)
(* (trsik : seq (k.-tuple sti * Sig * sti))                                    *)
(* (trsi : {ffun forall k : [r.+1], seq (k.-tuple sti * Sig * sti)})           *)
(* (Ai : tbuta r Sigma sti) (Ai' : tbuta ri Sigma sti), with i = 1, 2          *)
(*                                                                             *)
(* mergeable k trs1k trs2k == the list of pairs (tr1, tr2) such that           *)
(*                     tr1 \in trs1k, tr2 \in trs2k, and the labels of tr1 and *)
(*                     tr2 coincide                                            *)
(*         merge trs1 trs2 == the result of merging the transition functions   *)
(*                     tr1 and tr2                                             *)
(*     intersection1 A1 A2 == the automaton whose final states are all the     *)
(*                     pairs of final states from A1 and A2, and whose         *)
(*                     transition function is the merge of the transition      *)
(*                     functions of A1 and A2                                  *)
(*    intersection A1' A2' == the intersection1 of the restrictions of A1' and *)
(*                     A2' to the minumum between r1 and r2                    *)



Lemma addnmBm (n m : nat) : n + m - m = n.
Proof. by rewrite -{2}[m]/(0 + m) subnDr subn0. Qed.



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


Definition wdord (k : [r]) (j : [k]) : [r] :=
  widen_ord (ltnW (ltn_ord k)) j.

Definition maxo (m n : [r]) : [r] :=
  if m < n then n else m.

Definition subon (j : [r]) (n : nat) : [r].
Proof.
  refine (@Ordinal r (j - n) _).
  by move: j => [j jltr]; rewrite (leq_ltn_trans _ jltr) ?leq_subr.
Defined.
Notation "j -on k" := (subon j k) (at level 50, format "j  -on  k").


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
    have aa := subnS.
    have -> : j -on n.+1 = j -on n -on 1.
      by apply: val_inj; rewrite /= subnS subn1.
    by apply: wnU _ IH.
  move=> H; apply /allP; case => // a l alinU.
  by apply: (H _ a) => //; apply: leq_subr.
Qed.


Definition tree_like (U : ptree r) : bool :=
  [&& suffix_closed U, well_numbered U & uniq U].

Record tree := Tree {
  ptree_of_tree :> ptree r;
  _ : tree_like ptree_of_tree
}.

(* p is a parent of q                                                          *)
Definition is_parent (p q : [r*]) : bool := (parent q == p) && (q != [::]).

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

Definition children  (U : ptree r) (p : [r*]) : seq [r*] :=
  [seq s <- U | is_parent p s].

Definition arity (U : ptree r) (p : [r*]) : nat :=
  size (children U p).

Definition children_from_arity (p : [r.+1*]) (k : nat) :=
  [seq (inord i) :: p | i <- iota 0 k].

Definition children_from_arity_ord (p : [r*]) (k : [r]) : seq [r*] :=
  [seq (wdord i) :: p | i <- ord_enum k].

Definition children_from_arity_tuple (p : [r*]) (k : [r]) : k.-tuple [r*] :=
  [tuple (wdord i) :: p | i < k].

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
  all (fun p => ~~ (is_strict_ancestor s p)) U.

Definition leaves (U : ptree r) : seq [r*] :=
  [seq s <- U | is_leaf U s].

(* TODO maybe the empty S should also be connected *)
Definition connected (S : ptree r) : bool :=
  count (fun p => (p == [::]) || (parent p \notin S)) S == 1.

Lemma connected_correct (S : ptree r) (p : [r*]) :
  (p == [::]) || (parent p \notin S) =
  (p == [::]) || (p != [::]) && (parent p \notin S).
Proof. by case: p. Qed.

End Strings.

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

Lemma children_arityP (r : nat) (U : ptree r.+1) (p : [r.+1*]) :
    tree_like U ->
  perm_eq (children U p) (children_from_arity p (arity U p)).
Proof.
  move=> /and3P [scU /well_numberedP wnU uniqU].
  rewrite /children /children_from_arity.
  apply: uniq_perm; first by apply: filter_uniq.
    rewrite map_inj_in_uniq ?iota_uniq //= => n m.
    rewrite 2!mem_iota add0n => /andP [_ nlta] /andP [_ mlta] /eqP inpeqimp.
    have : @inord r n = @inord r m :> nat.
      congr val; move: inpeqimp.
      by rewrite eqseq_cons => /andP [/eqP].
    admit.
    (*
    rewrite inordK; last by rewrite (ltn_trans nlta) // arity_tree_like.
    by rewrite inordK; last by rewrite (ltn_trans mlta) // arity_tree_like.
    *)
  move=> /= s.
  apply /(@sameP (s \in [seq s0 <- U | is_parent p s0])); first by apply: idP.
  rewrite mem_filter.
  apply: (iffP idP).
    move=> /mapP /= [i]; rewrite mem_iota add0n => /andP [_ ilta] ->.
    apply /andP; split.
      by rewrite /is_parent andbT /parent /= drop0.
    admit.
  rewrite /is_parent.
  case: s; first by rewrite andbF.
  move=> j s.
  rewrite parent_cons => /andP [/andP [/eqP -> _] jpinU].
  apply /mapP => /=.
  exists j; last by rewrite inord_val.
  rewrite mem_iota; apply /andP; split => //.
  rewrite add0n /arity /children.
  rewrite size_filter.
  case: ltnP => // aUplej.
  (*
  set a := Ordinal (arity_tree_like U p).
  have := wnU _ _ jpinU a.
  *)


Admitted.


Section Tterms.

Variable r : nat.

(* Trees where each node has k children, and k is at most r                    *)
Inductive ttree : Type :=
| leaf : ttree
| node : forall k : [r.+1], ttree^k -> ttree.

Definition tarity (t : ttree) : [r.+1] :=
  match t with
  | leaf => ord0
  | node k _ => k
  end.

Fixpoint teq (t1 t2 : ttree) : bool :=
  match t1, t2 with
  | leaf, leaf => true
  | leaf, node _ _  | node _ _, leaf => false
  | node k1 f1, node k2 f2 => (k1 == k2) &&
      [forall i : [minn k1 k2],
          teq
            (f1 (widen_ord (geq_minl k1 k2) i))
            (f2 (widen_ord (geq_minr k1 k2) i))
      ]
  end.
Notation "t1 ==t t2" := (teq t1 t2) (at level 70).

Fixpoint tsub (s t : ttree) : bool :=
  match s, t with
  | leaf, leaf => true
  | leaf, node _ _ => false
  | node _ _, leaf => false
  | node _ _ as sn, node tk tf as tn => (sn ==t tn) ||
      [exists i : [tk], tsub sn (tf i)]
  end.
Notation "s \tin t" := (tsub s t) (at level 70).


Variable Sigma : finType.

Inductive tterm : Type :=
| tleaf : Sigma -> tterm
| tnode : Sigma -> forall k : [r.+1], tterm^k -> tterm.

(* We define a nested induction principle because the default one is too weak  *)
Fixpoint tterm_nind (P : tterm -> Prop)
    (Pleaf : forall a : Sigma, P (tleaf a))
    (Pnode : forall (a : Sigma) (k : [r.+1]) (f : tterm^k),
      (forall j : [k], P (f j)) -> P (tnode a f)
    )
    (t : tterm) : P t :=
  match t with
  | tleaf a => Pleaf a
  | tnode a k f => Pnode a k f (fun j => tterm_nind Pleaf Pnode (f j))
  end.

Definition head_sig (t : tterm) : Sigma :=
  match t with
  | tleaf a => a
  | tnode a _ _ => a
  end.

Fixpoint tpos (t : tterm) : ttree :=
  match t with
  | tleaf _ => leaf
  | tnode _ k f => @node k (finfun (tpos \o f))
  end.
Coercion tpos : tterm >-> ttree.

Fixpoint positions (t : tterm) : ptree r.+1 :=
  match t with
  | tleaf _ => [:: [::]]
  | tnode _ k ts =>
      [::] :: [seq rcons p (wdord j) |
        j <- ord_enum k,
        p <- positions (ts j)
      ]
  end.

Fixpoint positions_sig (t : tterm) : seq ([r.+1*] * Sigma) :=
  match t with
  | tleaf a => [:: ([::], a)]
  | tnode a k ts =>
      ([::], a) :: [seq (rcons pa.1 (wdord j), pa.2) |
        j <- ord_enum k,
        pa <- positions_sig (ts j)
      ]
  end.

Definition sig_at (d : Sigma) (t : tterm) (p : [r.+1*]) : Sigma :=
  (nth ([::], d)
    (positions_sig t)
    (find (fun pa => pa.1 == p) (positions_sig t))
  ).2.

Lemma positions_positions_sig (t : tterm) :
  positions t = [seq pa.1 | pa <- positions_sig t].
Proof.
  elim/tterm_nind: t => [// | a k f IH /=]; congr cons.
  rewrite map_allpairs /=.
  congr flatten; apply: eq_map => j.
  by rewrite IH -map_comp; apply: eq_map => [[]].
Qed.

Lemma sig_at_default (d d' : Sigma) (t : tterm) :
  {in positions t, sig_at d t =1 sig_at d' t}.
Proof.
  rewrite /sig_at /=.
  move=> p /nthP /= H; have := H [::] => {H} [[i iltsize] ithisp].
  set f := fun pa => _.
  congr snd.
  apply: set_nth_default; rewrite -has_find.
  move: iltsize ithisp; rewrite positions_positions_sig => iltsize.
  erewrite nth_map; last by move: iltsize; rewrite size_map.
  move=> nthpossig; apply /hasP => /=.
  exists (nth ([::], d) (positions_sig t) i).
    by apply: mem_nth; move: iltsize; rewrite size_map.
  by rewrite /f; apply /eqP; apply: nthpossig.
Qed.

Lemma positions_tree_like (t : tterm) : tree_like (positions t).
Proof.
  rewrite /tree_like; apply /and3P; split.
  - apply /suffix_closedP; case; first by case: t.
    elim/tterm_nind: t => //=.
    move=> _ k f IH j p i; rewrite 2!in_cons /= => /allpairsPdep /=.
    move=> [l [s [link s_in_posfl ijp_eq_rconssl]]].
    apply /allpairsPdep => /=.
    exists l; exists (behead s); split => //.
      admit.
    admit.
  - admit.
  - elim/tterm_nind: t => [// | a k ts IH /=].
    apply /andP; split.
      by apply /allpairsPdep => /= [[j [p [_ _]]]]; case p.
    apply: allpairs_uniq_dep; first exact: ord_enum_uniq.
      by move=> j _; apply: IH.
    by move=> [j1 p1] [j2 p2] _ _ /rcons_inj [p1e1p2 /ord_inj j1eqj2]; f_equal.

(*
  - apply /suffix_closedP; case => [// | j p i].
    rewrite lastI build_ptreeE /= (lastI j p) build_ptreeE.
    move: (validtrees (tnth _ (last j p)) (mem_tnth _ _)) => /and3P [].
    by move=> /suffix_closedP sc _ _; apply: sc.
  - apply /well_numberedP; case => [j | j p i].
      move=> _ k kltj; rewrite /build_ptree.
      rewrite lastI build_ptreeE /=.
      move: (validtrees (tnth trees k) (mem_tnth _ _)) => /and3P [sc _ _].
      apply: suffix_closed_nil => //.
      by apply: (nonempty _ (mem_tnth _ _)).
    rewrite lastI build_ptreeE /= => H k klti.
    rewrite lastI build_ptreeE /=.
    move: (validtrees (tnth _ (last j p)) (mem_tnth _ _)).
    move=> /and3P [_ /well_numberedP wn _].
    by apply: wn klti.
 *)
Admitted.

Definition tchildren (t : tterm) : seq tterm :=
  match t with
  | tleaf _ => [::]
  | tnode _ k ts => fgraph ts
  end.

(* TODO Lemma tchildren_children *)


End Tterms.

Section ToTtrees.

Variable r : nat.

Definition subtrees_of_ptree (U : ptree r.+1) (k : [r.+1]) :
    {ffun [k] -> ptree r.+1} :=
  [ffun i : [k] =>
    descendants_subtree U [:: wdord i]
  ].

Definition root_arity (U : ptree r.+1) : [r.+1] :=
  if [::] \in U then
    \big[@maxo r.+1/ord0]_(i <- [seq head ord0 p | p <- U & size p == 1]) i
  else
    ord0.

Lemma subtrees_of_ptree_size (U : ptree r.+1) (i : [root_arity U]) :
    [::] <> U ->
  size (subtrees_of_ptree U (root_arity U) i) < size U.
Proof.
  move=> eptyneqU.
  rewrite /subtrees_of_ptree ffunE size_map.
  move: i; rewrite /root_arity.
  case: ifP; last by move=> _ [].
  move=> eptyinU /= i; rewrite /descendants size_filter.
  have := count_size (is_ancestor [:: wdord i]) U.
  rewrite leq_eqVlt => /orP [| //].
  rewrite -all_count => allancestor; exfalso.
  move: allancestor; apply /negP; apply /allPn => /=.
  by exists [::].
Qed.

Program Fixpoint ttree_of_ptree (U : ptree r.+1) {measure (size U)}
    : ttree r :=
  match U with
  | [::] | [:: [::]] => leaf r
  | V => node [ffun i : [root_arity V] =>
      ttree_of_ptree (subtrees_of_ptree V (root_arity V) i)
    ]
  end.
Next Obligation.
  by apply /ltP; rewrite subtrees_of_ptree_size.
Qed.
Next Obligation.
  by split.
Qed.
Next Obligation.
  by split.
Qed.

End ToTtrees.

Section Automata.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.

Record tbuta : Type := {
  final : seq state;
  transitions : {ffun forall k : [r.+1], seq (k.-tuple state * Sigma * state)}
}.

Definition buta_size (A : tbuta) : nat :=
  #|state| + \sum_(k < r.+1) (size (transitions A k)).

Fixpoint reach_at_depth (A : tbuta) (q : state) (t : tterm r Sigma) (i : nat) :
    bool :=
  match i, t with
  | 0, _ => false
  | n.+1, tleaf a => ([tuple], a, q) \in transitions A ord0
  | n.+1, tnode a k f =>
    [exists tr in transitions A k,
      [&& tr.1.2 == a,
          tr.2 == q &
          [forall j : [k], reach_at_depth A (tnth tr.1.1 j) (f j) n]
      ]
    ]
  end.

Lemma reach_at_depth0 (A : tbuta) (q : state) (t : tterm r Sigma) :
  reach_at_depth A q t 0 = false.
Proof. by case: t. Qed.

Lemma reach_at_depth_leq (A : tbuta) (q : state) (t : tterm r Sigma)
      (i j : nat) :
    i <= j ->
    reach_at_depth A q t i ->
  reach_at_depth A q t j.
Proof.
  move: i; elim: j => [i | j IH i].
    by rewrite leqn0 => /eqP ->.
  case: ltngtP => [||->] //.
  move=> leij _ reachi.
  have := IH _ leij reachi => {i IH leij reachi}.
  case: j; move: q; elim/tterm_nind: t => //=.
  move=> a k f IH q n /'exists_and4P /= [[[qs a'] q'] /= [qsaq'_tran a'a q'q]].
  case: n.
    move: f IH qs qsaq'_tran; case: k => []; case.
      move=> lt0r1 f _ qs qsaq'_tran _.
      apply /'exists_and4P => /=; exists (qs, a', q'); split=> //.
      by apply /forallP => /= [[]].
    move=> k ltk1r1 f _ qs _.
    move=> reach0; exfalso; move: reach0; apply /negP; rewrite negb_forall.
    by apply /existsP => /=; exists ord0; rewrite reach_at_depth0.
  move=> n /forallP /= reachn1.
  apply /'exists_and4P => /=; exists (qs, a', q'); split=> //.
  by apply /forallP => /= j; apply: IH.
Qed.

Fixpoint reach_eventually (A : tbuta) (q : state) (t : tterm r Sigma) : bool :=
  match t with
  | tleaf a => ([tuple], a, q) \in transitions A ord0
  | tnode a k f =>
    [exists tr in transitions A k,
      [&& tr.1.2 == a,
          tr.2 == q &
          [forall j : [k], reach_eventually A (tnth tr.1.1 j) (f j)]
      ]
    ]
  end.

Lemma reach_at_depth_eventually (A : tbuta) (q : state) (t : tterm r Sigma) :
  reflect (exists i : nat, reach_at_depth A q t i) (reach_eventually A q t).
Proof.
  apply: (iffP idP) => [|[i]].
    move: t q; elim/tterm_nind => [a | a k f IH q].
      by exists 1.
    move=> /'exists_and4P /= [[[qs a'] q'] /= [qsaq'_tran a'a q'q]].
    rewrite -/reach_eventually => /forallP /= revent.
    have rdepth := IH _ _ (revent _) => {IH revent}.
    set m := \max_(j < k) (xchoose (rdepth j)); exists m.+1.
    apply /'exists_and4P => /=.
    exists (qs, a', q'); split=> //.
    apply /forallP => /= j.
    by apply: (reach_at_depth_leq _ (xchooseP (rdepth j))); apply: leq_bigmax.
  move: t q; elim i => [// | n IH]; case => //.
  move=> a k f q /'exists_and4P /= [[[qs a'] q'] /= [qsaq'_tran a'a q'q]].
  move=> /forallP /=; rewrite -/reach_at_depth => H.
  apply /'exists_and4P => /=.
  exists (qs, a', q'); split => //=.
  by apply /forallP => /= j; apply: IH; apply: H.
Qed.

Definition accepts (A : tbuta) (t : tterm r Sigma) : bool :=
  [exists q in final A, reach_eventually A q t].

Definition transitions_preim (A : tbuta) (q : state) :
    {ffun forall k : [r.+1], seq (k.-tuple state * Sigma * state)} :=
  [ffun k : [r.+1] => [seq tr <- transitions A k | tr.2 == q]].

Definition in_degree_state (A : tbuta) (q : state) : nat :=
  \sum_(k < r.+1) (size (transitions_preim A q k)).

Definition in_degree (A : tbuta) : nat :=
  \max_(q in state) (in_degree_state A q).

Definition deterministic (A : tbuta) : bool :=
  [forall k : [r.+1], forall qs : k.-tuple state, forall a : Sigma,
    count (fun tr => tr.1 == (qs, a)) (transitions A k) <= 1
  ].

End Automata.

Section Runs.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.
Variable A : tbuta r Sigma state.
Variable t : tterm r Sigma.

Definition wf_run (d : Sigma) (rho : [r.+1*] -> state) : bool :=
  all
    (fun p =>
      [forall (k : [r.+1] | k == arity (positions t) p :> nat),
        (
          [tuple of map rho (children_from_arity_tuple p k)],
          sig_at d t p,
          rho p
        ) \in transitions A k
      ]
    )
    (positions t).


Lemma wf_run_default (d d' : Sigma) (rho : [r.+1*] -> state) :
  wf_run d rho = wf_run d' rho.
Proof.
  rewrite /wf_run.
  apply: eq_in_all => p pinpos.
  by rewrite (sig_at_default d d' pinpos).
Qed.

Record trun := {
  trho : [r.+1*] -> state;
  _ : forall d, wf_run d trho
}.

Definition trun_size (rn : trun) : nat :=
  size (positions t).

Definition reaches_state (rn : trun) (q : state) : bool :=
  trho rn [::] == q.

Definition is_accepting (rn : trun) : bool :=
  has (reaches_state rn) (final A).

Definition reaches_transition (rn : trun) (k : [r.+1])
    (tr : k.-tuple state * Sigma * state) : bool :=
  (k == arity (positions t) [::] :> nat)
    &&
    (tr == (
      [tuple trho rn [:: wdord i] | i < k],
      (* the above line should be the same as using children_from_arity_tuple *)
      head_sig t,
      trho rn [::]
    )).

End Runs.

Definition unambiguous (r : nat) (Sigma state : finType)
  (A : tbuta r Sigma state) (d : Sigma) : Prop :=
  forall (t : tterm r Sigma) (rho1 rho2 : [r.+1*] -> state),
    wf_run A t d rho1 -> wf_run A t d rho2 -> {in positions t, rho1 =1 rho2}.

Lemma unambiguous_deterministic (r : nat) (Sigma state : finType)
  (A : tbuta r Sigma state) (d : Sigma) :
  deterministic A -> unambiguous A d.
Proof.
  rewrite /deterministic /unambiguous.
  move=> /'forall_'forall_forallP /= deterministicA t rho1 rho2.
  move=> /allP /= wf1 /allP /= wf2 p pinpos.
  set k := Ordinal (arity_tree_like p (positions_tree_like t)).
  have /'forall_implyP /= wf1p := wf1 p pinpos.
  have := wf1p k (eq_refl _) => {wf1 wf1p}.
  have /'forall_implyP /= wf2p := wf2 p pinpos.
  have := wf2p k (eq_refl _) => {wf2 wf2p}.
  set rho1c := [tuple of [seq rho1 i | i <- _]] : k.-tuple state.
  set rho2c := [tuple of [seq rho2 i | i <- _]].
  have <- : rho1c = rho2c.
    (* TODO proving this will require a bottom-up induction principle *)
    admit.
  have := deterministicA k rho1c (sig_at d t p) => {deterministicA rho2c}.
  set prd := fun tr : (k.-tuple state * Sigma * state) => _.
  have [/eqP // | neqrho12p] := boolP (rho1 p == rho2 p).
  set tr1 := (_, _, rho1 p) : (k.-tuple state * Sigma * state).
  set tr2 := (_, _, rho2 p) : (k.-tuple state * Sigma * state).
  have prd1 : prd tr1 by rewrite /prd.
  have prd2 : prd tr2 by rewrite /prd.
  move=> countlt1 tr2intr tr1intr.
  have transrm2 := perm_to_rem tr2intr.
  have tr1inrm : tr1 \in (tr2 :: rem tr2 (transitions A k)).
    by rewrite -(perm_mem transrm2).
  have transrm1 := perm_to_rem tr1inrm => {tr1inrm}.
  have /permP count_tran := perm_trans transrm2 transrm1 => {transrm1 transrm2}.
  move: countlt1; rewrite (count_tran prd) /= prd1 add1n.
  have -> /= : tr2 == tr1 = false.
    apply /eqP; rewrite /tr1 /tr2.
    move: neqrho12p => /eqP neqrho12p /pair_equal_spec [_ eqrho12p].
    by apply: neqrho12p.
  by rewrite prd2 add1n ltnS ltn0.
Admitted.

Section Intersection1.

Variable (r : nat).
Variable (Sig : finType).

Definition restrict (state : finType) (A : tbuta r Sig state) (n : nat)
    (nler : n < r.+1) : tbuta n Sig state :=
  {|
    final := final A;
    transitions := [ffun k : [n.+1] =>
      (transitions A (widen_ord nler k))
    ];
  |}.

Lemma restrict_self (state : finType) (A : tbuta r Sig state) :
  A = restrict A (ltnSn r).
Proof.
Admitted.

Variables (st1 st2 : finType).

(*   For now the automata are based on the same alphabet and have the same     *)
(* maximum arity.                                                              *)
Definition mergeable (k : nat) (trs1 : seq (k.-tuple st1 * Sig * st1))
    (trs2 : seq (k.-tuple st2 * Sig * st2)) :=
  [seq tr12 <- [seq (tr1, tr2) | tr1 <- trs1, tr2 <- trs2] |
      tr12.1.1.2 == tr12.2.1.2].

Definition merge
    (trs1 : {ffun forall k : [r.+1], seq (k.-tuple st1 * Sig * st1)})
    (trs2 : {ffun forall k : [r.+1], seq (k.-tuple st2 * Sig * st2)})
  : {ffun forall k : [r.+1], seq (k.-tuple (st1 * st2)%type * Sig * (st1 * st2))}
  :=
  [ffun k : [r.+1] =>
    [seq ([tuple of zip (val tr.1.1.1) (val tr.2.1.1)],
          tr.1.1.2,
          (tr.1.2, tr.2.2)
         ) | tr <- mergeable (trs1 k) (trs2 k)]
  ].

Definition intersection1 (A1 : tbuta r Sig st1) (A2 : tbuta r Sig st2) :
    tbuta r Sig (prod_finType st1 st2) :=
  {|
    final := [seq (f1, f2) | f1 <- (final A1), f2 <- (final A2)];
    transitions := merge (transitions A1) (transitions A2);
  |}.

Lemma intersection1_accepts (A1 : tbuta r Sig st1) (A2 : tbuta r Sig st2)
    (t : tterm r Sig) :
  accepts (intersection1 A1 A2) t = (accepts A1 t) && (accepts A2 t).
Proof.
Admitted.

End Intersection1.

Section Intersection.

Variables (r1 r2 : nat).
Variables (Sig : finType).
Variables (st1 st2 : finType).

Definition intersection (A1 : tbuta r1 Sig st1) (A2 : tbuta r2 Sig st2) :
    tbuta (minn r1 r2) Sig (prod_finType st1 st2) :=
  intersection1 (restrict A1 (geq_minl r1 r2)) (restrict A2 (geq_minr r1 r2)).

Lemma intersection_accepts (A1 : tbuta r1 Sig st1) (A2 : tbuta r2 Sig st2)
    (t : tterm (minn r1 r2) Sig) :
  accepts (intersection A1 A2) t =
    (accepts (restrict A1 (geq_minl r1 r2)) t)
    && (accepts (restrict A2 (geq_minr r1 r2)) t).
Proof.
  by rewrite intersection1_accepts.
Qed.

End Intersection.


(*******************************************************************************)
(* Below are old undocumented definitions that might be useful at some point   *)

Section Runs.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.
Variable A : tbuta r Sigma state.

(* FIXME *)
Fail Record run := {
  rterm : tterm r Sigma;
  rrho : [r.+1*] -> state;
  _ : forall (s : [r.+1*]), has_pos (tsterm_of_tterm rterm) s ->
    (
      [tuple of map rrho (children (positions rterm) s)],
      sig_at (tsterm_of_tterm rterm) s,
      rrho s
    ) \in transitions A (inord (size (children (positions rterm) s)));
}.

End Runs.

Section Terms.

Variable r : nat.
Variable X : finType.
Variable d : X.

(* Pre-terms, i.e., terms whose pos is not necessarily valid. *)
Record pterm := Pterm {
  pos : ptree r;
  assignment_of_pterm :> [r*] -> X;
}.

Definition pterm_code (t : pterm) : seq ([r*] * X) :=
  zip (pos t) (map t (pos t)).

Definition pterm_decode (AX : seq ([r*] * X)) : pterm :=
  Pterm (unzip1 AX) (fun s => (nth d (unzip2 AX) (index s (unzip1 AX)))).

Lemma pterm_codeK (t : pterm) (s : [r*]) :
  s \in pos t -> pterm_decode (pterm_code t) s = t s.
Proof.
  move: t => [post t].
  rewrite /pterm_code /pterm_decode /=.
  rewrite unzip2_zip ?size_map // unzip1_zip ?size_map //.
  elim: post => [// | a A IH].
  rewrite in_cons /=.
  case: ifP => [/eqP -> // | ].
  by rewrite eq_sym => ->.
Qed.

Definition eqt : rel pterm := fun t1 t2 =>
  pterm_code t1 == pterm_code t2.
Notation "t1 =t t2" := (eqt t1 t2) (at level 70, format "t1  =t  t2").

Definition build_ptree (trees : r.-tuple (ptree r)) : ptree r :=
  [::] :: [seq rcons p j | j <- ord_enum r, p <- (tnth trees j)].

Lemma rcons_nil (T : eqType) (p : seq T) (j : T) : (rcons p j == [::]) = false.
Proof. by case: p. Qed.
Hint Resolve rcons_nil : core.

Lemma build_ptreeE (trees : r.-tuple (ptree r)) (p : [r*]) (j : [r]) :
  (rcons p j \in build_ptree trees) = (p \in (tnth trees j)).
Proof.
  rewrite /build_ptree in_cons rcons_nil /=.
  have [pintreesj |] := boolP (p \in _).
    by apply /allpairsPdep; exists j; exists p; rewrite mem_ord_enum.
  apply: contraNF.
  by move=> /allpairsPdep /= [k [s [_ sintreesk /rcons_inj [-> ->]]]].
Qed.

Lemma build_tree_like (trees : r.-tuple (ptree r)) :
    all (fun tr => tr != [::]) trees ->
    all (@tree_like r) trees ->
  tree_like (build_ptree trees).
Proof.
  move=> /allP /= nonempty /allP /=.
  rewrite /tree_like => validtrees; apply /and3P; split.
  - apply /suffix_closedP; case => [// | j p i].
    rewrite lastI build_ptreeE /= (lastI j p) build_ptreeE.
    move: (validtrees (tnth _ (last j p)) (mem_tnth _ _)) => /and3P [].
    by move=> /suffix_closedP sc _ _; apply: sc.
  - apply /well_numberedP; case => [j | j p i].
      move=> _ k kltj; rewrite /build_ptree.
      rewrite lastI build_ptreeE /=.
      move: (validtrees (tnth trees k) (mem_tnth _ _)) => /and3P [sc _ _].
      apply: suffix_closed_nil => //.
      by apply: (nonempty _ (mem_tnth _ _)).
    rewrite lastI build_ptreeE /= => H k klti.
    rewrite lastI build_ptreeE /=.
    move: (validtrees (tnth _ (last j p)) (mem_tnth _ _)).
    move=> /and3P [_ /well_numberedP wn _].
    by apply: wn klti.
  - rewrite /build_ptree cons_uniq; apply /andP; split.
      by apply /allpairsPdep => [[j [p [_ _ /eqP]]]]; rewrite eq_sym rcons_nil.
    apply: allpairs_uniq_dep.
    + exact: ord_enum_uniq.
    + by move=> k _; move: (validtrees (tnth _ k) (mem_tnth _ _)) => /and3P [].
    + by move=> /= [j1 p1] [j2 p2] _ _ /rcons_inj [p1e1p2 j1eqj2]; f_equal.
Qed.

Definition break_ptree (t : ptree r) : (r.-tuple (ptree r)).
Admitted.

Definition build_pterm (a : X) (ts : r.-tuple pterm) : pterm :=
  let post := build_ptree [tuple of map pos ts] in
  let t (s : [r*]) :=
    if s is j :: p then (tnth ts (last j p)) (belast j p) else a
  in
  Pterm post t.

(* FIXME probably needs some more assumptions *)
Lemma build_correct (a : X) (ts : r.-tuple pterm) (s : [r*]) (i : [r]) :
    s \in pos (build_pterm a ts) ->
  (build_pterm a ts) (rcons s i) = (tnth ts i) s.
Proof.
  have : rcons s i = rcons s i by [].
  case: {2}(rcons s i) => [/eqP | j p eqrconsjp].
    by rewrite rcons_nil.
  rewrite eqrconsjp /=.
Admitted.

(* FIXME This is silly because pos could have type tree *)
Record term := Term {
  term_of_pterm :> pterm;
  _ : tree_like (pos term_of_pterm);
}.

End Terms.

Definition break_pterm (r : nat) (Sigma : finType) (t : pterm r Sigma) :
  Sigma * (r.-tuple (pterm r Sigma)).
Admitted.

Section Automata.

Variable (r m : nat).
Variable (Sigma state : finType).

(* Pre-bottom up tree automaton *)
Record pbuta := mkButa {
  final_states : seq state;
  (* The k-ary transitions are given by (transitions k) *)
  trans : forall (n : [m.+1]), seq (n.-tuple state * Sigma * state);
}.

Definition valid_buta (A : pbuta) : bool :=
  (uniq (final_states A)).

Definition tasize (A : pbuta) : nat :=
  #|state| + \sum_(n < m.+1) (size (trans A n)).

(* The term (build a ts) reaches state q in depth at most i. *)
(*
Fixpoint reach (A : pbuta) (k : [m.+1]) (t : pterm k Sigma)
    (q : state) (i : nat) : bool :=
  let (a, ts) := break_pterm t in
  match i with
  | 0 => false
  | 1 => (k == ord0) && (([tuple], a, q) \in (trans A ord0))
  | (n.+1 as n').+1 => [exists tran in (trans A k),
              [&& tran.1.2 == a,
                  tran.2 == q &
                  [forall j in [k],
                      reach A (tnth ts j) (tnth tran.1.1 j) n'
                  ]
              ]
            ]
  end.
*)

End Automata.

(*     tsterm Sigma == structural terms based on seq instead of tuple with     *)
(*                     constructors                                            *)
(*                     - tsnone                                                *)
(*                     - tsleaf a                                              *)
(*                     - tsnode a ts                                           *)
(*                     where (a : Sigma) is a label and (ts : seq tsterm) is a *)
(*                     list of children                                        *)
(*      tsterm_of_tterm t == the tsterm corresponding to t                     *)
(*      sig_at t' s == if s is a position in t', this outputs Some a where a   *)
(*                     is the label found at that position; otherwise outputs  *)
(*                     None                                                    *)
(*     has_pos t' s == s is a position in t'                                   *)

Section Tsterms.

Variable Sigma : finType.

Inductive tsterm : Type :=
| tsnone : tsterm
| tsleaf : Sigma -> tsterm
| tsnode : Sigma -> seq tsterm -> tsterm.

Variable (r : nat).

Fixpoint tsterm_of_tterm (t : tterm r Sigma) : tsterm :=
  match t with
  | tleaf a => tsleaf a
  | tnode a k ts => tsnode a [seq tsterm_of_tterm (ts i) | i <- ord_enum k]
  end.

(*
Print Finfun.
Print tterm.
Fixpoint tterm_of_tsterm (t' : tsterm) : option (tterm r Sigma) :=
  match t' with
  | tsnone => None
  | tsleaf a => Some (tleaf r a)
  | tsnode a w => Some (tnode a (Finfun (in_tuple (map tterm_of_tsterm w))))
  end.
*)

Local Fixpoint ts_sig_at_aux (t : tsterm) (revs : [r*]) : option Sigma :=
  match revs, t with
  | _, tsnone => None
  | [::], tsleaf a | [::], tsnode a _ => Some a
  | _ :: _, tsleaf _ => None
  | j :: p, tsnode a ts => ts_sig_at_aux (nth tsnone ts j) p
  end.

Definition ts_sig_at (t : tsterm) (s : [r*]) : option Sigma :=
  ts_sig_at_aux t (rev s).

Definition ts_has_pos (t : tsterm) (s : [r*]) : bool :=
  isSome (ts_sig_at t s).

End Tsterms.

Lemma positions_has_pos (r : nat) (Sigma : finType) (t : tterm r Sigma)
     (s : [r.+1*]) :
   (s \in positions t) = (ts_has_pos (tsterm_of_tterm t) s).
Proof.
Admitted.

Section Psubtrees.

Variable r : nat.

Definition psubtrees_of_ptree (U : ptree r.+1) : seq ([r.+1] * ptree r.+1) :=
  [seq (head ord0 p, descendants_subtree U p) | p <- [seq u <- U | size u == 1]].

Definition psubtrees_of_ptree_sorted (U : ptree r.+1) :=
  [seq np.2 |
    np <- sort
            (fun (np mq : [r.+1] * ptree r.+1) => np.1 <= mq.1)
            (psubtrees_of_ptree U)
  ].

Lemma size_take_ord (T : Type) (w : seq T) :
  size (take r w) <= r.
Proof. by rewrite size_take; case: ltnP. Qed.

Fail Fixpoint ttree_of_ptree (U : ptree r.+1) : ttree r :=
  let subs := psubtrees_of_ptree_sorted U in
  if subs is [::] then leaf r
  else
    @node r
      (@Ordinal r.+1 (size (take r (map ttree_of_ptree subs))) (size_take_ord (map ttree_of_ptree subs)))
      (@Finfun (ordinal_finType r.+1) _ (in_tuple (take r (map ttree_of_ptree subs)))).

End Psubtrees.

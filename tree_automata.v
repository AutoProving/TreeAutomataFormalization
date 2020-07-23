Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*   This library is heavily based upon mathcomp.ssreflect libraries such as:  *)
(*     https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html         *)
(*     https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html     *)
(*     https://math-comp.github.io/htmldoc/mathcomp.ssreflect.tuple.html       *)
(*                                                                             *)
(*                                                                             *)
(*   Here are short descriptions of currently implemented functionality.       *)
(*   Let (r : nat), (j, k : [r]) (p, q, s : [r*]), and (U : ptree)             *)
(*                                                                             *)
(*                                 DATATYPES                                   *)
(*              nat == the natural numbers                                     *)
(*              [r] == the natural numbers smaller than r (aka the ordinal r)  *)
(*             [r*] == the type of finite strings over [r]                     *)
(*          ptree r == the type of lists of [r*]                               *)
(*             [::] == the empty list (or string depending on its type)        *)
(*           j :: p == a string corresponding to prepending j to p             *)
(* [:: j1; ...; jn] == the string with the elements j1 to jn                   *)
(*                                                                             *)
(*   The following coercions are available:                                    *)
(*   - From [r] to nat                                                         *)
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

(* p is a parent of q *)
Definition is_parent (p q : [r*]) : bool := parent p == q.

(* p is a child of q *)
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

Definition children  (U : ptree r) (p : [r*]) : seq [r*] :=
  [seq s <- U | is_parent p s].

Definition descendants (U : ptree r) (p : [r*]) : seq [r*] :=
  [seq s <- U | is_ancestor p s].

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
  transitions : forall (n : [m.+1]), seq (n.-tuple state * Sigma * state);
}.

Definition valid_buta (A : pbuta) : bool :=
  (uniq (final_states A)).

Definition tasize (A : pbuta) : nat :=
  #|state| + \sum_(n < m.+1) (size (transitions A n)).

About break_pterm.
(* The term (build a ts) reaches state q in depth at most i. *)
Fixpoint reach (A : pbuta) (k : [m.+1]) (t : pterm k Sigma)
    (q : state) (i : nat) : bool :=
  let (a, ts) := break_pterm t in
  match i with
  | 0 => false
  | 1 => (k == ord0) && (([tuple], a, q) \in (transitions A ord0))
  | (n.+1 as n').+1 => [exists tran in (transitions A k),
              [&& tran.1.2 == a,
                  tran.2 == q &
                  [forall j in [k],
                      reach A (tnth ts j) (tnth tran.1.1 j) n'
                  ]
              ]
            ]
  end.

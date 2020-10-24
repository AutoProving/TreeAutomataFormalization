Set Warnings "-notation-overridden, -notation-incompatible-format".
From mathcomp Require Import all_ssreflect finmap.
Set Warnings "notation-overridden, notation-incompatible-format".

Require Import Coq.Program.Wf.

Require Import basic.
Require Import trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************************)
(*   This library is heavily based upon mathcomp.ssreflect libraries such as:  *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html         *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html     *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.tuple.html       *)
(*   - https://math-comp.github.io/htmldoc/mathcomp.ssreflect.finfun.html      *)
(*   and on the finmap library:                                                *)
(*   - https://github.com/math-comp/finmap/blob/master/finmap.v                *)
(*                                                                             *)
(*                                                                             *)
(*   Here are short descriptions of the functionality currently implemented.   *)
(*                                                                             *)
(*                                                                             *)
(*                           *** TREE-BASED TYPES ***                          *)
(*                                                                             *)
(*   Let (T : Type) (r i n : nat) (Sigma : finType) (d : Sigma)                *)
(* (t : tterm r Sigma) (state : finType) (q : state) (A : tbuta r Sigma state) *)
(* (t' : tsterm).                                                              *)
(*                                                                             *)
(*                                    TERMS                                    *)
(*          ttree r == structural trees with constructors                      *)
(*                     - leaf                                                  *)
(*                     - node k f                                              *)
(*                     where (k : [[r.+1]]) is the arity of the node (i.e., the  *)
(*                     number of children) and (f : ttree^k) is a finite       *)
(*                     function assigning a child to each (j : [[k]])            *)
(*       ttree_nind == a nested induction principle for ttree (the standard    *)
(*                     one is as weak as a case analysis)                      *)
(*    tterm r Sigma == structural terms with constructors                      *)
(*                     - tleaf a                                               *)
(*                     - tnode a k f                                           *)
(*                     where (a : Sigma) is a label, (k : [[r.+1]]) is the arity *)
(*                     of the node and (f : tterm^k) is as above               *)
(*       tterm_nind == a nested induction principle for tterm (the standard    *)
(*                     one is as weak as a case analysis)                      *)
(*       head_sig t == the label of the root of t                              *)
(*           tpos t == the ttree obtained from t by forgeting the labels       *)
(*      positions t == the ptree corresponding to t                            *)
(*    fsig_at d t p == the label found at position p of t, or d if p is not a  *)
(*                     position of t                                           *)
(*        child_ind == an induction principle for terms starting from the      *)
(*                     leaves and using positions                              *)
(*                                                                             *)
(*                                  AUTOMATA                                   *)
(*    tbuta r Sigma state == bottom-up tree automata with the following fields *)
(*                     - (final : seq state) represents the final (i.e.,       *)
(*                       accepting) states                                     *)
(*                     - (transitions : {ffun forall k : [[r.+1]],               *)
(*                         seq (k.-tuple state * Sigma * state)})              *)
(*                       represents the transition function. Thus,             *)
(*                       (transitions k) is the list of the transitions with   *)
(*                       arity k                                               *)
(*     tbuta_uniq A == true iff there are no repeated transitions in A         *)
(*     buta r Sigma state == a uniq tbuta with constructor BUTA                *)
(*      buta_size A == the size of the automaton A, equal to the sum of the    *)
(*                     number of states with the number of unique transitions  *)
(* reach_at_depth A q t i == in the automaton A, term t reaches state q in at  *)
(*                     most i steps                                            *)
(* reach_eventually A q t == in A, t eventually reaches q                      *)
(*      accepts A t == t eventually reaches one of the final states of A       *)
(*  transitions_preim A q == the transitions of A that have q as a consequent  *)
(*    in_degree_state A q == the number of transitions of A that have q as a   *)
(*                     consequent                                              *)
(*      in_degree A == the maximum in-degree of any given state of A           *)
(*  deterministic A == for each tuple of states qs and label a, there is at    *)
(*                     most one state q such that (qs, a, q) is a transition   *)
(*                     of A                                                    *)
(* restrict r Sigma state A n (nler : n <= r) == the (tbuta n Sigma state)     *)
(*                     automaton corresponding to A without the transitions    *)
(*                     with greater than n arity                               *)
(*                                                                             *)
(*                                     RUNS                                    *)
(*   Let (A : tbuta r.+1 Sigma state) (t t' : tterm r.+1 Sigma) (d : Sigma)    *)
(* (rho : [[r.+1*]] -> state) (rn : trun A t) (rn' : trun A t').                 *)
(*                                                                             *)
(*  wfrun A t d rho == for each position p of t, if cs are the children of p,  *)
(*                     then (map rho cs, fsig_at d t p, rho p) is a transition *)
(*                     of A                                                    *)
(*         trun A t == a function trho such that (t, trho) is                  *)
(*                     (wfrun A t d rho) for every d                           *)
(*     trun_size rn == the number of positions of the term of the run          *)
(*      reaches_state rn q == the state reached at the root is q               *)
(*  is_accepting rn == the run rn reaches some accepting state                 *)
(* reaches_transition rn k tr == the run rn reaches the k-transition k         *)
(*  unambiguous A d == for each term t there is at most one rho such that      *)
(*                     (wfrun A t d rho) holds                                 *)
(* extends A t t' rn rn' d == there is a string p that can be appended to each *)
(*                     position of t to obtain the behaviour of rn'            *)
(*                                                                             *)
(*                                INTERSECTION                                 *)
(*   Let (st1 st2 : finType)  (r1 r2 : nat)                                    *)
(* (trsik : seq (k.-tuple sti * Sig * sti))                                    *)
(* (trsi : {ffun forall k : [[r.+1]], seq (k.-tuple sti * Sig * sti)})           *)
(* (Ai : tbuta r Sigma sti) (Ai' : tbuta ri Sigma sti), with i = 1, 2.         *)
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


Section Tterms.

Variable r : nat.

(* Trees where each node has k children, and k is at most r                    *)
Inductive ttree : Type :=
| leaf : ttree
| node : forall k : [r.+1], ttree^k -> ttree.

(* We define a nested induction principle because the default one is too weak  *)
Fixpoint ttree_nind (P : ttree -> Prop)
    (Pleaf : P leaf)
    (Pnode : forall (k : [r.+1]) (f : ttree^k),
      (forall j : [k], P (f j)) -> P (node f)
    )
    (t : ttree) : P t :=
  match t with
  | leaf => Pleaf
  | node k f => Pnode k f (fun j => ttree_nind Pleaf Pnode (f j))
  end.

(*
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
*)

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

(*
Fixpoint ptree_of_ttree (t : ttree) : ptree r :=
  match t with
  | leaf => [:: [::]]
  | node k ts =>
      [::] :: [seq rcons p (wdord j) |
        j <- ord_enum k,
        p <- ptree_of_ttree (ts j)
      ]
  end.
*)

Fixpoint positions (t : tterm) : ptree r :=
  match t with
  | tleaf _ => [:: [::]]
  | tnode _ k ts =>
      [::] :: [seq rcons p (wdord j)  |
        j <- ord_enum k,
        p <- positions (ts j)
      ]
  end.

Fixpoint fsig_at (dSigma : Sigma) (t : tterm) (p : [r*]) : Sigma :=
   match t, p with
   | tleaf a, [::] => a
   | tleaf a, _ :: _ => dSigma
   | tnode a k f, [::] => a
   | tnode a k f, j :: p =>
       oapp
         (fun i => fsig_at dSigma (f i) (belast j p))
         dSigma
         (insub (val (last j p)))
   end.

Lemma fsig_at_path (dSigma a : Sigma) (k : [r.+1]) (f : tterm^k) (p : [r*])
    (j : [k]) :
  fsig_at dSigma (tnode a f) (rcons p (wdord j)) = fsig_at dSigma (f j) p.
Proof.
  rewrite headI /= last_headI belast_headI insubT /= ?ltn_ord // => ltjk.
  by have -> : Ordinal ltjk = j by apply /val_eqP.
Qed.

Lemma fsig_at_head (d : Sigma) (t : tterm) :
  fsig_at d t [::] = head_sig t.
Proof. by case: t. Qed.

Lemma fsig_at_default (d d' : Sigma) (t : tterm) :
  {in positions t, fsig_at d t =1 fsig_at d' t}.
Proof.
Admitted.

Lemma positions_nil (t : tterm) :
  [::] \in positions t.
Proof. by case: t. Qed.

Lemma positions_tnode (a : Sigma) (k : [r.+1]) (f : tterm^k) (p : [r*]) :
    p \in positions (tnode a f) ->
  p = [::] \/
    exists (j : [k]) (q : [r*]), p = rcons q (wdord j) /\ q \in positions (f j).
Proof.
  rewrite /= in_cons => /orP [/eqP -> |]; first by left.
  move=> /allpairsPdep /= [j [q [_ qinposfj eqpjq]]].
  by right; exists j; exists q; split.
Qed.

Lemma positions_child (a : Sigma) (k : [r.+1]) (f : tterm^k) (p : [r*])
    (j : [k]) :
  (p \in positions (f j)) = (rcons p (wdord j) \in positions (tnode a f)).
Proof.
  rewrite /= in_cons rcons_nil /=; apply /idP /idP => [pinposfj |].
   by apply: allpairs_f_dep => //; apply mem_ord_enum.
  move=> /allpairsPdep /= [i [q [_ qinposfi /eqP]]].
  rewrite eqseq_rcons => /andP [/eqP -> wdij]; move: wdij.
  by rewrite wdord_eq => /eqP ->.
Qed.

Lemma positions_last (a : Sigma) (k : [r.+1]) (f : tterm^k) (j : [r]) (p : [r*]) :
    j :: p \in positions (tnode a f) ->
  last j p < k.
Proof.
  rewrite /= in_cons /= => /allpairsPdep /= [i [q [_ qinpos /eqP]]].
  by rewrite lastI eqseq_rcons => /andP [_ /eqP ->] /=; apply: ltn_ord.
Qed.

Lemma positions_tree_like (t : tterm) : tree_like (positions t).
Proof.
  apply /tree_likeP; split.
  - apply /suffix_closedP.
    elim/tterm_nind: t => [// | a k f IH].
    case/lastP => [| p j i ipjinpos].
      by rewrite positions_nil.
    have ltjk : j < k.
      by move: ipjinpos => /positions_last; rewrite last_rcons.
    move: ipjinpos.
    have -> : j = wdord (Ordinal ltjk) by apply /val_eqP.
    rewrite -rcons_cons -2!positions_child.
    by apply: IH.
  - apply /well_numberedP.
    elim/tterm_nind: t => [// | a k f IH].
    case/lastP => [j | q i j jqiinpos l lelj].
       move=> /positions_tnode [// | [i [q [/eqP]]]].
      rewrite lastI eqseq_rcons => /= /andP [/eqP <- /eqP ->] _ l leli.
      rewrite in_cons /=; apply /allpairsPdep => /=.
      have ltlk : l < k.
        by rewrite (leq_ltn_trans leli) //; apply: (ltn_ord i).
      exists (Ordinal ltlk); exists [::]; rewrite mem_ord_enum; split => //=.
        by apply: positions_nil.
      by congr cons; apply /val_eqP.
    have ltik : i < k.
      by move: jqiinpos; move=> /positions_last; rewrite last_rcons.
    move: jqiinpos.
    have -> : i = wdord (Ordinal ltik) by apply /val_eqP.
    rewrite -2!rcons_cons -2!positions_child => jqinposi.
    by apply: (IH _ _ j).
  - elim/tterm_nind: t => [// | a k ts IH /=].
    apply /andP; split.
      by apply /allpairsPdep => /= [[j [p [_ _]]]]; case p.
    apply: allpairs_uniq_dep; first exact: ord_enum_uniq.
      by move=> j _; apply: IH.
    by move=> [j1 p1] [j2 p2] _ _ /rcons_inj [p1e1p2 /ord_inj j1eqj2]; f_equal.
Qed.

(*
(*      tchildren t == a list of the children of t as tterms                   *)
Definition tchildren (t : tterm) : seq tterm :=
  match t with
  | tleaf _ => [::]
  | tnode _ k ts => fgraph ts
  end.

(* Lemma tchildren_children *)
*)

End Tterms.

Section Tterms2.

Variable r : nat.
Variable Sigma : finType.

Lemma child_ind (P : [r.+1*] -> Prop) (Q : tterm r.+1 Sigma -> Prop)
  (Pleaves : forall (t : tterm r.+1 Sigma), Q t ->
    forall (l : [r.+1*]), l \in positions t ->
      is_leaf (positions t) l -> P l
  )
  (Pchildren : forall (t : tterm r.+1 Sigma), Q t ->
    forall (p : [r.+1*]), p \in positions t ->
      (forall q : [r.+1*],
        q \in children_from_arity p (arity (positions t) p) -> P q
      ) -> P p
  )
  (t : tterm r.+1 Sigma) (Qt : Q t) (p : [r.+1*]) (pinpos : p \in positions t)
  : P p.
Proof.
  apply: (@ptree_buind _ (positions t)) => //.
  - by apply: positions_tree_like.
  - by move=> l linpos lleaf; apply: (Pleaves t).
  - move=> q qinpos IH.
    by apply: (Pchildren t) => // c /children_from_arityP [i ->]; apply: IH.
Qed.

Lemma children_indexesE (a : Sigma) (k : [r.+2]) (f : (tterm r.+1 Sigma)^k) :
  perm_eq
    (children_indexes (positions (tnode a f)) [::])
    [seq wdord i | i <- enum [k]].
Proof.
  apply: uniq_perm.
  - by rewrite children_indexes_uniq // positions_tree_like.
  - by rewrite map_inj_uniq ?enum_uniq //; apply: wdord_inj.
  Opaque positions.
  move=> i; apply /idP /idP.
    move=> /mapP /= [c /childrenP [/is_parentP [j ->] jpinpos] ->] /=.
    apply /mapP => /=.
    exists (Ordinal (positions_last jpinpos)).
      by rewrite mem_enum inE.
    by apply /val_eqP => /=.
  move=> /mapP /= [j _ ->].
  apply /mapP => /=; exists [:: wdord j] => //.
  Transparent positions.
  apply /childrenP; rewrite /is_parent /=; split => //=.
  rewrite in_cons /=; apply /allpairsPdep => /=.
  exists j; exists [::] => /=.
  by rewrite mem_ord_enum positions_nil.
Qed.

Lemma bigmax_enum (n : nat) :
  \max_(x <- enum [n.+1]) x = n.
Proof.
  Opaque iota.
  rewrite -(big_map val [pred x | true] id) val_enum_ord /=.
  Transparent iota.
  have iota_perm : forall n, perm_eq (iota 0 n.+1) (n :: (iota 0 n)).
    move=> m; apply: uniq_perm; first by rewrite iota_uniq.
      by rewrite cons_uniq iota_uniq andbT mem_iota add0n /= -leqNgt.
    move=> i; rewrite mem_iota in_cons mem_iota 2!add0n leq0n /=.
    by rewrite ltnS leq_eqVlt.
  elim: n => [| n IH]; first by rewrite big_cons big_nil.
  rewrite (perm_big _ (iota_perm _)) /= big_cons IH.
  by apply /maxn_idPl.
Qed.

Lemma arity_positions (a : Sigma) (k : [r.+2]) (f : (tterm r.+1 Sigma)^k) :
  arity (positions (tnode a f)) [::] = k.
Proof.
  move: f; case: k; case=> [lt0r2 f | n ltn1r2 f].
    by rewrite /arity /=; apply /val_eqP.
  have ltnr1 : n < r.+1 by [].
  rewrite /arity children_map.
  Opaque positions.
  case eqchildren : (children_indexes _ _) => [/= | i cs /=].
    move: eqchildren => /perm_nilP.
    move: (children_indexesE a f).
    rewrite perm_sym => H1 H2.
    have := perm_trans H1 H2.
    rewrite /= => /perm_nilP /(f_equal size) /=.
    by rewrite size_map size_enum_ord.
  have -> : Ordinal ltn1r2 = So (Ordinal ltnr1) by apply /val_eqP.
  congr So.
  apply /val_eqP /eqP; rewrite /= /max -bmaxn_bmaxo -map_cons -eqchildren.
  rewrite (perm_big _ (perm_map _ (children_indexesE _ _))) /=.
  do 2!rewrite bigmax_map -map_comp -bigmax_map /=.
  by rewrite bigmax_enum.
Qed.

Lemma children_from_arity_positions (t : tterm r.+1 Sigma) (p q : [r.+1*]) :
    p \in positions t ->
    q \in children_from_arity p (arity (positions t) p) ->
  q \in positions t.
Proof.
  move=> pinpos /children_from_arityP [i ->].
  by apply: mem_child => //; apply: positions_tree_like.
Qed.

Lemma arity_path (a : Sigma) (k : [r.+2]) (f : (tterm r.+1 Sigma)^k)
    (p : [r.+1*]) (j : [k]) :
  arity (positions (tnode a f)) (rcons p (wdord j)) =
  arity (positions (f j)) p.
Proof.
  apply /val_eqP /eqP; rewrite 2!val_arity /arity_nat.
  set cspj := children _ (rcons _ _).
  set csp := children _ _.
  suff: [seq nat_of_ord (head ord0 c) | c <- cspj] =i
        [seq nat_of_ord (head ord0 c) | c <- csp].
    case eqcspj : cspj => [| cpj ccpj].
      by case: csp => //= ? ? /eq_mem0c.
    case eqcsp : csp => [/= | cp ccp]; first by move=> /eq_memc0.
    move=> eqi; congr S.
    rewrite bigmax_map [in RHS]bigmax_map.
    by apply: eq_big_idem => //; apply: maxnn.
  move=> c; apply /mapP /mapP.
    move=> [q /childrenP [/is_parentP [i ->] qinpos] ->].
    exists (i :: p) => //.
    by apply /childrenP; rewrite is_parent_trivial (positions_child a).
  move=> [q /childrenP [/is_parentP [i ->] qinpos] ->].
  exists (i :: rcons p (wdord j)) => //.
  by apply /childrenP; rewrite is_parent_trivial -rcons_cons -positions_child.
Qed.

End Tterms2.

Section Automata.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.

Record tbuta : Type := {
  final : seq state;
  transitions : {ffun forall k : [r.+1], seq (k.-tuple state * Sigma * state)}
}.

Definition tbuta_uniq (A : tbuta) : bool :=
  [forall k : [r.+1], uniq (transitions A k)].

Lemma tbuta_uniqP (A : tbuta) :
  reflect
    (forall k : [r.+1], uniq (transitions A k))
    (tbuta_uniq A).
Proof. by apply: (iffP forallP). Qed.

Record buta : Type := BUTA {
  tbuta_of_buta :> tbuta;
  _ : tbuta_uniq tbuta_of_buta;
}.
Canonical buta_subType := [subType for tbuta_of_buta].

Lemma buta_uniq (A : buta) : tbuta_uniq A.
Proof. by case: A. Qed.

Lemma buta_uniq_trans (A : buta) (k : [r.+1]) :
  uniq (transitions A k).
Proof. by have /tbuta_uniqP /(_ k) := buta_uniq A. Qed.

Lemma buta_undup (A : buta) (k : [r.+1]) :
  undup (transitions A k) = transitions A k.
Proof. by apply: undup_id; apply: buta_uniq_trans. Qed.

Definition buta_size (A : tbuta) : nat :=
  #|state| + \sum_(k < r.+1) (size (undup (transitions A k))).

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

Lemma reach_eventuallyP (A : tbuta) (q : state) (t : tterm r Sigma) :
  reflect
    (match t with
     | tleaf a => ([tuple], a, q) \in transitions A ord0
     | tnode a k f =>
       exists tr,
         [/\ tr \in transitions A k,
             tr.1.2 = a,
             tr.2 = q &
             forall j : [k], reach_eventually A (tnth tr.1.1 j) (f j)
         ]
     end
    )
    (reach_eventually A q t).
Proof.
  case: t => /=  [a | a k f].
    by apply: (iffP idP).
  apply: (iffP 'exists_and4P) => /=.
    by move=> [tr [? /eqP ? /eqP ? /forallP ?]]; exists tr; split.
  by move=> [tr [? /eqP ? /eqP ? /forallP ?]]; exists tr; split.
Qed.

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

Lemma acceptsP (A : tbuta) (t : tterm r Sigma) :
  reflect
    (exists q, q \in final A /\ reach_eventually A q t)
    (accepts A t).
Proof. by apply: (iffP 'exists_andP). Qed.

Definition transitions_preim (A : tbuta) (q : state) :
    {ffun forall k : [r.+1], seq (k.-tuple state * Sigma * state)} :=
  [ffun k : [r.+1] => [seq tr <- undup (transitions A k) | tr.2 == q]].

Definition in_degree_state (A : tbuta) (q : state) : nat :=
  \sum_(k < r.+1) (size (transitions_preim A q k)).

Definition in_degree (A : tbuta) : nat :=
  \max_(q in state) (in_degree_state A q).

Definition deterministic (A : tbuta) : bool :=
  [forall k : [r.+1], forall qs : k.-tuple state, forall a : Sigma,
    count (fun tr => tr.1 == (qs, a)) (transitions A k) <= 1
  ].

Lemma deterministicP (A : buta) :
  reflect
    (forall (k : [r.+1]) (qs : k.-tuple state) (a : Sigma) (q1 q2 : state),
        (qs, a, q1) \in transitions A k ->
        (qs, a, q2) \in transitions A k ->
      q1 = q2
    )
    (deterministic A).
Proof.
  apply: (iffP 'forall_'forall_forallP) => /=.
    move=> H k qs a q1 q2.
    set tr1 := (qs, a, q1); set tr2 := (qs, a, q2); move=> tr1trasn tr2trans.
    have := H k qs a.
    set f := fun tr => _ => countlt1.
    have f1 : f tr1 by rewrite /f.
    have f2 : f tr2 by rewrite /f.
    have transrm2 := perm_to_rem tr2trans.
    have tr1inrm : tr1 \in (tr2 :: rem tr2 (transitions A k)).
      by rewrite -(perm_mem transrm2).
    have transrm1 := perm_to_rem tr1inrm => {tr1inrm}.
    have /permP counttran := perm_trans transrm2 transrm1 => {transrm1 transrm2}.
    move: countlt1; rewrite (counttran f) /= f1 add1n.
    case: ifP => [/eqP [] // | /eqP neqtr1tr2 /=].
    by rewrite f2 add1n ltnS ltn0.
  move=> H k qs a.
  set f := fun tr => _.
  rewrite -size_filter.
  case isfilter : (filter f (transitions A k)) => [// | tr1 trs].
  rewrite -isfilter size_filter.
  have tr1infilter : tr1 \in filter f (transitions A k).
    by rewrite isfilter mem_head.
  have ftr1 : f tr1.
    by move: tr1infilter; rewrite mem_filter => /andP [].
  have subftr1 : {in transitions A k, subpred f (pred1 tr1)}.
    move=> /= tr trintrans; rewrite /f => /eqP eqtr1qsa.
    rewrite (surjective_pairing tr1) (surjective_pairing tr) eqtr1qsa.
    have eqtr11qsa : tr1.1 = (qs, a) by move: ftr1; rewrite /f => /eqP ->.
    rewrite eqtr11qsa; apply /eqP; rewrite pair_equal_spec; split => //.
    apply: (H k qs a); first by rewrite -eqtr1qsa -surjective_pairing.
    rewrite -eqtr11qsa -surjective_pairing.
    by move: tr1infilter; rewrite mem_filter => /andP [].
  rewrite (leq_trans (sub_in_count subftr1)) //.
  by rewrite count_uniq_mem ?leq_b1 ?buta_uniq_trans.
Qed.

End Automata.


Section Runs.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.
Variable A : tbuta r.+1 Sigma state.

Definition wfrun (t : tterm r.+1 Sigma) (d : Sigma)
    (rho : [r.+1*] -> state) : bool :=
  all
    (fun p : [r.+1*] =>
      (
        [tuple of map rho (children_from_arity p (arity (positions t) p))],
        fsig_at d t p,
        rho p
      ) \in transitions A (arity (positions t) p)
    )
    (positions t).

Lemma wfrun_default (t : tterm r.+1 Sigma) (d d' : Sigma)
    (rho : [r.+1*] -> state) :
  wfrun t d rho = wfrun t d' rho.
Proof.
  rewrite /wfrun.
  apply: eq_in_all => p pinpos.
  by rewrite (fsig_at_default d d' pinpos).
Qed.

Lemma wfrunP (t : tterm r.+1 Sigma) (d : Sigma) (rho : [r.+1*] -> state) :
  reflect
    {in positions t, forall p,
      (
        [tuple of map rho (children_from_arity p (arity (positions t) p))],
        fsig_at d t p,
        rho p
      ) \in transitions A (arity (positions t) p)
    }
    (wfrun t d rho).
Proof.
  by apply: (iffP allP).
Qed.

(*
Definition partial_run (rho : [r.+1*] -> state) (j : [r.+1])
    : [r.+1*] -> state :=
  fun p => rho (j :: p).

Lemma partial_wfrun (rho : [r.+1*] -> state) (a : Sigma) (k : [r.+2])
  (f : (tterm r.+1 Sigma)^k) (d : Sigma) :
    wfrun (tnode a f) d rho ->
  forall (j : [k]), wfrun (f j) d (partial_run rho (wdord j)).
Proof.
Admitted.
*)

Variable t : tterm r.+1 Sigma.
Variable dstate : state.
Variable dSigma : Sigma.

Record frun := FRun {
  frho :> {fsfun [r.+1*] -> state with dstate};
  _ : wfrun t dSigma frho
}.
Canonical frun_subType := [subType for frho].
Definition frun_eqMixin := [eqMixin of frun by <:].
Canonical frun_eqType := EqType frun frun_eqMixin.
Definition frun_choiceMixin := [choiceMixin of frun by <:].
Canonical frun_choiceType := ChoiceType frun frun_choiceMixin.

Lemma frun_wfrun (rn : frun) : wfrun t dSigma (frho rn).
Proof. by case: rn. Qed.

Definition frun_size (rn : frun) : nat :=
  size (positions t).

Definition reaches_state (rn : frun) (q : state) : bool :=
  rn [::] == q.

Definition is_accepting (rn : frun) : bool :=
  has (reaches_state rn) (final A).

Lemma is_acceptingP (rn : frun) :
  reflect
    (exists2 q, q \in final A & reaches_state rn q)
    (is_accepting rn).
Proof.
  by apply /(iffP hasP).
Qed.

Definition reaches_transition (rn : frun) (k : [r.+2])
    (tr : k.-tuple state * Sigma * state) : bool :=
  (k == arity (positions t) [::] :> nat)
    &&
    (tr == (
      [tuple frho rn [:: wdord i] | i < k],
      (* the above line should be the same as using children_from_arity *)
      head_sig t,
      rn [::]
    )).

End Runs.

Section Acceptance.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.
Variable A : tbuta r.+1 Sigma state.
Variable dstate : state.
Variable dSigma : Sigma.

Local Open Scope fset.

Definition fpos (t : tterm r.+1 Sigma) : {fset [r.+1*]} :=
  [fset p | p in positions t].

Lemma in_fpos (t : tterm r.+1 Sigma) (p : [r.+1*]) :
  (p \in fpos t) = (p \in positions t).
Proof. by rewrite in_fsetE. Qed.

Lemma fpos_nil (t : tterm r.+1 Sigma) :
  [::] \in fpos t.
Proof. by rewrite in_fpos positions_nil. Qed.

(*
Definition ffsig_at (t : tterm r.+1 Sigma) :=
  [fsfun p in (fpos t) => fsig_at t p | dSigma].
*)

Lemma reaches_state_eventually (t : tterm r.+1 Sigma) (q : state) :
  reflect
    (exists (rn : frun A t dstate dSigma), reaches_state rn q)
    (reach_eventually A q t).
Proof.
  apply: (iffP idP).
    move: q; elim/tterm_nind: t.
      move=> a q /reach_eventuallyP aqintrans.
      rewrite /reaches_state.
      pose rho := [fsfun p : fpos (tleaf r.+1 a) => q | dstate].
      have rho0 : rho [::] = q by rewrite fsfun_fun fpos_nil.
      suff wfrho : wfrun A (tleaf r.+1 a) dSigma rho.
        by exists (FRun wfrho); rewrite rho0.
      apply /wfrunP => /= p.
      by rewrite arity0 tuple0 mem_seq1 => /eqP ->; rewrite rho0.
    move=> a k f IH q /reach_eventuallyP /= [tr [trintrans tra trq trqs]].
    pose rho := [fsfun p in fpos (tnode a f) =>
      if p is j' :: s then
       oapp
         (fun j =>
            let rhoj := xchoose (IH j (tnth tr.1.1 j) (trqs j)) in
            rhoj (belast j' s)
         )
         dstate
         (insub (val (last j' s)))
      else q
    | dstate].
    suff wfrho : wfrun A (tnode a f) dSigma rho.
      by exists (FRun wfrho); rewrite /reaches_state fsfun_fun fpos_nil.
    apply /wfrunP => p pinpos.
    have /positions_tnode [-> | [j [s [eqpsj sinpos]]]] := pinpos.
      rewrite arity_positions fsfun_fun fpos_nil /=.
      set qs := [tuple of _].
      suff -> : qs = tr.1.1 by rewrite -tra -trq -2!surjective_pairing.
      apply: eq_from_tnth => i.
      rewrite tnth_map tnth_children_from_arity.
      rewrite fsfun_fun /=.
      have -> : [:: wdord i] \in fpos (tnode a f).
        rewrite in_fpos -[[:: wdord i]]/(rcons [::] (wdord i)).
        by rewrite -positions_child positions_nil.
      rewrite insubT ?ltn_ord //= => ltik; rewrite ordinalE.
      set IHi := IH _ _ _.
      by have /eqP -> := xchooseP IHi.
    rewrite fsfun_fun in_fpos pinpos eqpsj.
    rewrite [X in (_, _, match X with [::] => _ | _ :: _ => _ end)]headI.
    rewrite last_headI belast_headI insubT => [/= | ltjk].
      by rewrite /= ltn_ord.
    Opaque children_from_arity positions fsig_at.
    rewrite /=.
    Transparent children_from_arity positions fsig_at.
    rewrite ordinalE.
    set IHj := IH _ _ _.
    have := xchooseP IHj.
    set rhoj := xchoose IHj => /eqP reachesj.
    have /wfrunP /(_ s) /(_ sinpos) := frun_wfrun rhoj.
    rewrite arity_path fsig_at_path.
    set qsj := [tuple of _].
    set qs := [tuple of _].
    suff -> : qsj = qs by [].
    apply: eq_from_tnth => i.
    do 2!rewrite tnth_map tnth_children_from_arity.
    rewrite fsfun_fun.
    have -> : wdord i :: rcons s (wdord j) \in fpos (tnode a f).
      rewrite in_fpos -rcons_cons -positions_child.
      by apply: mem_child => //; apply: positions_tree_like.
    by rewrite last_rcons belast_rcons insubT /= ordinalE.
  move: q; elim/tterm_nind: t => [a q [rn /eqP rnnilq] | a k f IH q].
    apply /reach_eventuallyP.
    have /wfrunP /= /(_ [::]) /(_ isT) := frun_wfrun rn.
    by rewrite arity0 tuple0 rnnilq.
  move=> [rn /eqP rnnilq]; apply /reach_eventuallyP => /=.
  exists ([tuple of [seq rn i | i <- children_from_arity [::] k]], a, q).
  Opaque children_from_arity.
  rewrite /=; split=> //.
    have /wfrunP /(_ [::]) /(_ (positions_nil _)) := frun_wfrun rn.
    by rewrite rnnilq arity_positions.
  Transparent children_from_arity.
  move=> j; rewrite tnth_map tnth_children_from_arity.
  apply: IH.
  rewrite /reaches_state.
  pose rho := [fsfun p in fpos (f j) => rn (rcons p (wdord j)) | dstate].
  suff wfrho : wfrun A (f j) dSigma rho.
    by exists (FRun wfrho); rewrite fsfun_fun fpos_nil.
  apply /wfrunP => /= p pinpos.
  have /wfrunP /(_ (rcons p (wdord j))) := frun_wfrun rn.
  rewrite -positions_child => /(_ pinpos).
  rewrite fsig_at_path arity_path fsfun_fun in_fpos pinpos.
  set qspj := [tuple of _].
  set qsp := [tuple of _].
  suff -> : qspj = qsp by [].
  apply: eq_from_tnth => i.
  do 2!rewrite tnth_map tnth_children_from_arity.
  by rewrite fsfun_fun in_fpos rcons_cons mem_child ?positions_tree_like.
Qed.

Lemma accepts_is_accepting (t : tterm r.+1 Sigma) :
  reflect
    (exists (rn : frun A t dstate dSigma), is_accepting rn)
    (accepts A t).
Proof.
  apply: (iffP idP).
    move=> /acceptsP [q [qinfinal /reaches_state_eventually [rn reachesrn]]].
    by exists rn; apply /hasP; exists q.
  move=> [rn /hasP [q qinfinal reachesrnq]].
  apply /acceptsP; exists q; split=> //.
  by apply /reaches_state_eventually; exists rn.
Qed.

End Acceptance.

Section Unambiguous.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.

Definition unambiguous (A : tbuta r.+1 Sigma state) (d : Sigma) : Prop :=
  forall (t : tterm r.+1 Sigma) (rho1 rho2 : [r.+1*] -> state),
    wfrun A t d rho1 -> wfrun A t d rho2 -> {in positions t, rho1 =1 rho2}.

Lemma unambiguous_deterministic (A : buta r.+1 Sigma state) (d : Sigma) :
  deterministic A -> unambiguous A d.
Proof.
  move=> /deterministicP deterA.
  move=> t rho1 rho2 wf1 wf2 /=.
  have {wf1 wf2} : wfrun A t d rho1 /\ wfrun A t d rho2 by split.
  move: t; apply: child_ind => /=.
    move=> t [wf1 wf2] l linpos lleaf.
    apply: deterA.
      by move: wf1 => /wfrunP /(_ l) /(_ linpos); apply.
    have := wf2 => /wfrunP /(_ l) /(_ linpos).
    by rewrite arity_leaf // children_from_arity0 (report_bug _ rho1); apply.
  move=> t [wf1 wf2] p pinpos IH; apply: deterA.
    by move: wf1 => /wfrunP /(_ p) /(_ pinpos); apply.
  have := wf2 => /wfrunP /(_ p) /(_ pinpos).
  set tup1 := [tuple of [seq rho1 _ | _ <- _]].
  set tup2 := [tuple of [seq rho2 _ | _ <- _]].
  suff -> : tup1 = tup2 by apply.
  rewrite -eq_in_map_tuple => /= s sinchildren.
  by apply: IH.
Qed.

End Unambiguous.

Section Runs2.

Variable r : nat.
Variable Sigma : finType.
Variable state : finType.
Variable A : tbuta r.+1 Sigma state.
Variable dstate : state.
Variable dSigma : Sigma.

Definition extends (t t' : tterm r.+1 Sigma) (rn : frun A t dstate dSigma)
    (rn' : frun A t' dstate dSigma) : Prop :=
  exists p : [r.+1*], forall u : [r.+1*],
      u \in positions t ->
    (fsig_at dSigma t u = fsig_at dSigma t' (u ++ p))
    /\ (frho rn u = frho rn' (u ++ p)).

End Runs2.

Section AutomataComposition1.

Variable (r : nat).
Variable (Sig : finType).

Definition restrict (state : finType) (A : tbuta r.+1 Sig state) (n : nat)
    (nler : n.+1 < r.+2) : tbuta n.+1 Sig state :=
  {|
    final := final A;
    transitions := [ffun k : [n.+2] =>
      (transitions A (widen_ord nler k))
    ];
  |}.

Lemma restrict_uniq (state : finType) (A : buta r.+1 Sig state) (n : nat)
      (nler : n.+1 < r.+2) :
  tbuta_uniq (restrict A nler).
Proof.
Admitted.

Lemma restrict_self (state : finType) (A : tbuta r.+1 Sig state) :
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
    (trs1 : {ffun forall k : [r.+2], seq (k.-tuple st1 * Sig * st1)})
    (trs2 : {ffun forall k : [r.+2], seq (k.-tuple st2 * Sig * st2)})
  : {ffun forall k : [r.+2], seq (k.-tuple (st1 * st2)%type * Sig * (st1 * st2))}
  :=
  [ffun k : [r.+2] =>
    [seq ([tuple of zip (val tr.1.1.1) (val tr.2.1.1)],
          tr.1.1.2,
          (tr.1.2, tr.2.2)
         ) | tr <- mergeable (trs1 k) (trs2 k)]
  ].

Lemma in_merge
    (trs1 : {ffun forall k : [r.+2], seq (k.-tuple st1 * Sig * st1)})
    (trs2 : {ffun forall k : [r.+2], seq (k.-tuple st2 * Sig * st2)})
    (k : [r.+2]) (qs : k.-tuple (st1 * st2)) (a : Sig) (q : st1 * st2) :
  (qs, a, q) \in merge trs1 trs2 k
    = (([tuple of unzip1 qs], a, q.1) \in trs1 k) && (([tuple of unzip2 qs], a, q.2) \in trs2 k).
Proof.
  rewrite ffunE.
  apply /mapP /andP => /=.
    move=> [x]; rewrite /mergeable mem_filter => /andP [/eqP eqSig].
    move=> /allpairsP /= [y [y1 y2] eqxy] /=.
    move: eqSig; rewrite eqxy => /= eqSig.
    rewrite 2!pair_equal_spec => [[[-> ->] ->]] /=.
    have -> : [tuple of unzip1 (zip y.1.1.1 y.2.1.1)] = y.1.1.1.
      by apply /val_eqP => /=; rewrite unzip1_zip // 2!size_tuple.
    have -> : [tuple of unzip2 (zip y.1.1.1 y.2.1.1)] = y.2.1.1.
      by apply /val_eqP => /=; rewrite unzip2_zip // 2!size_tuple.
    by rewrite {2}eqSig -!surjective_pairing.
  move=> [tr1in1 tr2in2].
  exists (([tuple of unzip1 qs], a, q.1), ([tuple of unzip2 qs], a, q.2)).
    rewrite /mergeable mem_filter /= eqxx /=.
    apply /allpairsP => /=.
    by exists (([tuple of unzip1 qs], a, q.1), ([tuple of unzip2 qs], a, q.2)).
  rewrite /= -surjective_pairing 2!pair_equal_spec; do 2!split=> //.
  by apply /val_eqP => /=; rewrite zip_unzip.
Qed.

Lemma in_merge_exp
    (trs1 : {ffun forall k : [r.+2], seq (k.-tuple st1 * Sig * st1)})
    (trs2 : {ffun forall k : [r.+2], seq (k.-tuple st2 * Sig * st2)})
    (k : [r.+2]) (qs1 : k.-tuple st1) (qs2 : k.-tuple st2) (a : Sig) (q1 : st1)
    (q2 : st2) :
  ([tuple of zip qs1 qs2], a, (q1, q2)) \in merge trs1 trs2 k
    = ((qs1, a, q1) \in trs1 k) && ((qs2, a, q2) \in trs2 k).
Proof.
  rewrite in_merge /=.
  have -> : [tuple of unzip1 (zip qs1 qs2)] = qs1.
    by apply /val_eqP => /=; rewrite unzip1_zip // 2!size_tuple.
  have -> : [tuple of unzip2 (zip qs1 qs2)] = qs2.
    by apply /val_eqP => /=; rewrite unzip2_zip // 2!size_tuple.
  by [].
Qed.

Definition intersection1 (A1 : tbuta r.+1 Sig st1) (A2 : tbuta r.+1 Sig st2) :
    tbuta r.+1 Sig (prod_finType st1 st2) :=
  {|
    final := [seq (f1, f2) | f1 <- (final A1), f2 <- (final A2)];
    transitions := merge (transitions A1) (transitions A2);
  |}.

Lemma intersection1_uniq (A1 : buta r.+1 Sig st1) (A2 : buta r.+1 Sig st2) :
  tbuta_uniq (intersection1 A1 A2).
Proof.
Admitted.

Definition union1 (A1 : tbuta r.+1 Sig st1) (A2 : tbuta r.+1 Sig st2) :
    tbuta r.+1 Sig (prod_finType st1 st2) :=
  {|
    final := [seq (f1, f2) | f1 <- (final A1), f2 <- enum st2]
             ++ [seq (f1, f2) | f1 <- enum st1, f2 <- (final A2)];
    transitions := merge (transitions A1) (transitions A2);
  |}.

Lemma union1_uniq (A1 : buta r.+1 Sig st1) (A2 : buta r.+1 Sig st2) :
  tbuta_uniq (union1 A1 A2).
Proof.
Admitted.

Variable dst1 : st1.
Variable dst2 : st2.
Variable dSig : Sig.

Lemma intersection1_accepts (A1 : tbuta r.+1 Sig st1) (A2 : tbuta r.+1 Sig st2)
    (t : tterm r.+1 Sig) :
  accepts (intersection1 A1 A2) t = (accepts A1 t) && (accepts A2 t).
Proof.
  apply /(accepts_is_accepting _ (dst1, dst2) dSig) /andP.
    move=> [rni /is_acceptingP /= [qs /allpairsP [[q1 q2] /= [q1f q2f ->]]]].
    rewrite /reaches_state=> /eqP rnnil; split.
      apply /(accepts_is_accepting _ dst1 dSig).
      pose rho1 := [fsfun p in fpos t => (rni p).1 | dst1].
      suff wfrho1 : wfrun A1 t dSig rho1.
        exists (FRun wfrho1); apply /is_acceptingP; exists q1 => //.
        by rewrite /reaches_state fsfun_fun fpos_nil rnnil.
      apply /wfrunP => p pinpos.
      move: (frun_wfrun rni) => /wfrunP /(_ p) /(_ pinpos).
      rewrite in_merge => /andP [inA1 _]; move: inA1.
      rewrite fsfun_fun in_fpos pinpos.
      congr in_mem; rewrite 2!pair_equal_spec; split=> //; split=> //.
      apply: eq_from_tnth => i.
      rewrite 3!tnth_map tnth_children_from_arity fsfun_fun in_fpos mem_child //.
      by rewrite positions_tree_like.
    (* TODO this is a lot of code repetition *)
    apply /(accepts_is_accepting _ dst2 dSig).
    pose rho2 := [fsfun p in fpos t => (rni p).2 | dst2].
    suff wfrho2 : wfrun A2 t dSig rho2.
      exists (FRun wfrho2); apply /is_acceptingP; exists q2 => //.
      by rewrite /reaches_state fsfun_fun fpos_nil rnnil.
    apply /wfrunP => p pinpos.
    move: (frun_wfrun rni) => /wfrunP /(_ p) /(_ pinpos).
    rewrite in_merge => /andP [_].
    rewrite fsfun_fun in_fpos pinpos.
    congr in_mem; rewrite 2!pair_equal_spec; split=> //; split=> //.
    apply: eq_from_tnth => i.
    rewrite 3!tnth_map tnth_children_from_arity fsfun_fun in_fpos mem_child //.
    by rewrite positions_tree_like.
Admitted.

Lemma union1_accepts (A1 : tbuta r.+1 Sig st1) (A2 : tbuta r.+1 Sig st2)
    (t : tterm r.+1 Sig) :
  accepts (union1 A1 A2) t = (accepts A1 t) || (accepts A2 t).
Proof.
  apply /(accepts_is_accepting _ (dst1, dst2) dSig) /orP.
    move=> [rni /is_acceptingP /= [qs]].
    rewrite mem_cat => /orP [/allpairsP [[q1 q2] /= [q1f _ ->]] |].
      rewrite /reaches_state=> /eqP rnnil; left.
      (* TODO this is a lot of code repetition *)
      apply /(accepts_is_accepting _ dst1 dSig).
      pose rho1 := [fsfun p in fpos t => (rni p).1 | dst1].
      suff wfrho1 : wfrun A1 t dSig rho1.
        exists (FRun wfrho1); apply /is_acceptingP; exists q1 => //.
        by rewrite /reaches_state fsfun_fun fpos_nil rnnil.
      apply /wfrunP => p pinpos.
      move: (frun_wfrun rni) => /wfrunP /(_ p) /(_ pinpos).
      rewrite in_merge => /andP [inA1 _]; move: inA1.
      rewrite fsfun_fun in_fpos pinpos.
      congr in_mem; rewrite 2!pair_equal_spec; split=> //; split=> //.
      apply: eq_from_tnth => i.
      rewrite 3!tnth_map tnth_children_from_arity fsfun_fun in_fpos mem_child //.
      by rewrite positions_tree_like.
    move=> /allpairsP [[q1 q2] /= [_ qf2 ->]].
    rewrite /reaches_state=> /eqP rnnil; right.
    (* TODO this is a lot of code repetition *)
    apply /(accepts_is_accepting _ dst2 dSig).
    pose rho2 := [fsfun p in fpos t => (rni p).2 | dst2].
    suff wfrho2 : wfrun A2 t dSig rho2.
      exists (FRun wfrho2); apply /is_acceptingP; exists q2 => //.
      by rewrite /reaches_state fsfun_fun fpos_nil rnnil.
    apply /wfrunP => p pinpos.
    move: (frun_wfrun rni) => /wfrunP /(_ p) /(_ pinpos).
    rewrite in_merge => /andP [_].
    rewrite fsfun_fun in_fpos pinpos.
    congr in_mem; rewrite 2!pair_equal_spec; split=> //; split=> //.
    apply: eq_from_tnth => i.
    rewrite 3!tnth_map tnth_children_from_arity fsfun_fun in_fpos mem_child //.
    by rewrite positions_tree_like.
Admitted.

End AutomataComposition1.

Section AutomataComposition.

Variables (r1 r2 : nat).
Variables (Sig : finType).
Variables (st1 st2 : finType).

Definition intersection (A1 : tbuta r1.+1 Sig st1) (A2 : tbuta r2.+1 Sig st2) :
    tbuta (minn r1 r2).+1 Sig (prod_finType st1 st2) :=
  intersection1 (restrict A1 (geq_minlS r1 r2)) (restrict A2 (geq_minrS r1 r2)).

Lemma intersection_uniq (A1 : buta r1.+1 Sig st1) (A2 : buta r2.+1 Sig st2) :
  tbuta_uniq (intersection A1 A2).
Proof.
Admitted.

Definition union (A1 : tbuta r1.+1 Sig st1) (A2 : tbuta r2.+1 Sig st2) :
    tbuta (minn r1 r2).+1 Sig (prod_finType st1 st2) :=
  union1 (restrict A1 (geq_minlS r1 r2)) (restrict A2 (geq_minrS r1 r2)).

Lemma union_uniq (A1 : buta r1.+1 Sig st1) (A2 : buta r2.+1 Sig st2) :
  tbuta_uniq (union A1 A2).
Proof.
Admitted.

Variable dst1 : st1.
Variable dst2 : st2.
Variable dSig : Sig.

Lemma intersection_accepts (A1 : tbuta r1.+1 Sig st1)
    (A2 : tbuta r2.+1 Sig st2)
    (t : tterm (minn r1 r2).+1 Sig) :
  accepts (intersection A1 A2) t =
    (accepts (restrict A1 (geq_minlS r1 r2)) t)
    && (accepts (restrict A2 (geq_minrS r1 r2)) t).
Proof.
  by rewrite intersection1_accepts.
Qed.

Lemma union_accepts (A1 : tbuta r1.+1 Sig st1)
    (A2 : tbuta r2.+1 Sig st2)
    (t : tterm (minn r1 r2).+1 Sig) :
  accepts (union A1 A2) t =
    (accepts (restrict A1 (geq_minlS r1 r2)) t)
    || (accepts (restrict A2 (geq_minrS r1 r2)) t).
Proof.
  by rewrite union1_accepts.
Qed.

End AutomataComposition.

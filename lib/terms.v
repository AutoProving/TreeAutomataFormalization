Set Warnings "-notation-overridden, -notation-incompatible-format".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-format".

Require Import Coq.Program.Wf.

Require Import Trees.

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


Fixpoint ptree_of_ttree (t : ttree) : ptree r :=
  match t with
  | leaf => [:: [::]]
  | node k ts =>
      [::] :: [seq rcons p (wdord j) |
        j <- ord_enum k,
        p <- ptree_of_ttree (ts j)
      ]
  end.

Fixpoint positions (t : tterm) : ptree r :=
  match t with
  | tleaf _ => [:: [::]]
  | tnode _ k ts =>
      [::] :: [seq (wdord j) :: p  |
        j <- ord_enum k,
        p <- positions (ts j)
      ]
  end.

Fixpoint positions_sig (t : tterm) : seq ([r*] * Sigma) :=
  match t with
  | tleaf a => [:: ([::], a)]
  | tnode a k ts =>
      ([::], a) :: [seq ((wdord j) :: pa.1, pa.2) |
        j <- ord_enum k,
        pa <- positions_sig (ts j)
      ]
  end.

Definition sig_at (d : Sigma) (t : tterm) (p : [r*]) : Sigma :=
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

Lemma positions_tnode (a : Sigma) (k : [r.+1]) (f : tterm^k) (p : [r*]) :
    p \in positions (tnode a f) ->
  p = [::] \/
    exists (j : [k]) (q : [r*]), p = wdord j :: q /\ q \in positions (f j).
Proof.
  rewrite /= in_cons => /orP [/eqP -> |]; first by left.
  move=> /allpairsPdep /= [j [q [_ qinposfj eqpjq]]].
  by right; exists j; exists q; split.
Qed.

Lemma positions_child (a : Sigma) (k : [r.+1]) (f : tterm^k) (p : [r*])
    (j : [k]) :
  (p \in positions (f j)) = (wdord j :: p \in positions (tnode a f)).
Proof.
  rewrite /= in_cons /=; apply /idP /idP => [pinposfj |].
    by apply: allpairs_f_dep => //; apply mem_ord_enum.
  move=> /allpairsPdep /= [i [q [_ qinposfi /eqP]]].
  rewrite eqseq_cons => /andP [wdij /eqP ->]; move: wdij.
  by rewrite wdord_eq => /eqP ->.
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
    by move=> /= [j1 p1] [j2 p2] _ _ [/ord_inj -> ->].

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

Lemma positions_nil (t : tterm) :
  [::] \in positions t.
Proof.
  apply: tree_like_nil.
    by apply: positions_tree_like.
  by case: t.
Qed.

Definition tchildren (t : tterm) : seq tterm :=
  match t with
  | tleaf _ => [::]
  | tnode _ k ts => fgraph ts
  end.

(* TODO Lemma tchildren_children *)


End Tterms.

Section ToTtrees.

Definition subtrees_of_ptree (r : nat) (U : ptree r) (k : [r.+1]) :
    {ffun [k] -> ptree r} :=
  [ffun i : [k] =>
    descendants_subtree U [:: wdord i]
  ].

Variable r : nat.

(*
Definition root_arity (U : ptree r.+1) : [r.+1] :=
  if [::] \in U then
    \big[@maxo r.+1/ord0]_(i <- [seq head ord0 p | p <- U & size p == 1]) i
  else
    ord0.
*)


Lemma subtrees_of_ptree_size (U : ptree r.+1) (i : [arity U [::]]) :
    [::] <> U ->
  size (subtrees_of_ptree U (arity U [::]) i) < size U.
Proof.
  move=> eptyneqU.
  rewrite /subtrees_of_ptree ffunE size_map.
  (*
  move: i; rewrite /arity.
  case: ifP; last by move=> _ [].
  move=> eptyinU /= i; rewrite /descendants size_filter.
  have := count_size (is_ancestor [:: wdord i]) U.
  rewrite leq_eqVlt => /orP [| //].
  rewrite -all_count => allancestor; exfalso.
  move: allancestor; apply /negP; apply /allPn => /=.
  by exists [::].
  *)
Admitted.

Program Fixpoint ttree_of_ptree (U : ptree r.+1) {measure (size U)}
    : ttree r.+1 :=
  match U with
  | [::] | [:: [::]] => leaf r.+1
  | V => node [ffun i : [arity V [::]] =>
      ttree_of_ptree (subtrees_of_ptree V (arity V [::]) i)
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

Lemma ttree_of_ptree_eq (U : ptree r.+1) : ttree_of_ptree U =
  match U with
  | [::] | [:: [::]] => leaf r.+1
  | V => node [ffun i : [arity V [::]] =>
      ttree_of_ptree (subtrees_of_ptree V (arity V [::]) i)
    ]
  end.
Proof.
  rewrite /ttree_of_ptree fix_sub_eq.
    rewrite -/ttree_of_ptree /=.
    by case: U => //=; case => //=; case.
  case => //=; case.
    case => //=.
    move=> a l f g feq1g; congr node.
    by rewrite -ffunP /= => x; rewrite ffunE; symmetry; rewrite ffunE feq1g.
    (* TODO report symmetry bug? *)
  move=> a l V f g feq1g; congr node.
  by rewrite -ffunP /= => x; rewrite ffunE; symmetry; rewrite ffunE feq1g.
Qed.

Lemma ptree_of_ttreeK : cancel (@ptree_of_ttree r.+1) ttree_of_ptree.
Proof.
  elim/ttree_nind => [// | k f IH /=]; rewrite ttree_of_ptree_eq.
  case w : [seq _ | _ <- _, _ <- _].
    exfalso; move: w.
    admit.
  move: w => <-.
  set rarty := arity _ _.
  have -> : rarty = k.
    admit.
  congr node.
  rewrite -ffunP /= => j; rewrite ffunE -IH.
Admitted.

Lemma ttree_of_ptreeK (U : ptree r.+1) :
    tree_like U ->
  U = ptree_of_ttree (ttree_of_ptree U).
Proof.
Admitted.

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

Lemma deterministicP (A : tbuta) :
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
  case: ltnP => //.
  have {H} := H k; elim: (transitions A k) => [// | x tr IH H /=].
  admit.
Admitted.

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
        sig_at d t p,
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
  by rewrite (sig_at_default d d' pinpos).
Qed.

Lemma wfrunP (t : tterm r.+1 Sigma) (d : Sigma) (rho : [r.+1*] -> state) :
  reflect
    {in positions t, forall p,
      (
        [tuple of map rho (children_from_arity p (arity (positions t) p))],
        sig_at d t p,
        rho p
      ) \in transitions A (arity (positions t) p)
    }
    (wfrun t d rho).
Proof.
  by apply: (iffP allP).
Qed.

Definition partial_run (rho : [r.+1*] -> state) (j : [r.+1])
    : [r.+1*] -> state :=
  fun p => rho (j :: p).

Lemma partial_wfrun (rho : [r.+1*] -> state) (a : Sigma) (k : [r.+2])
  (f : (tterm r.+1 Sigma)^k) (d : Sigma) :
    wfrun (tnode a f) d rho ->
  forall (j : [k]), wfrun (f j) d (partial_run rho (wdord j)).
Proof.
Admitted.

Variable t : tterm r.+1 Sigma.

Record trun := {
  trho : [r.+1*] -> state;
  _ : forall d, wfrun t d trho
}.

Definition trun_size (rn : trun) : nat :=
  size (positions t).

Definition reaches_state (rn : trun) (q : state) : bool :=
  trho rn [::] == q.

Definition is_accepting (rn : trun) : bool :=
  has (reaches_state rn) (final A).

Definition reaches_transition (rn : trun) (k : [r.+2])
    (tr : k.-tuple state * Sigma * state) : bool :=
  (k == arity (positions t) [::] :> nat)
    &&
    (tr == (
      [tuple trho rn [:: wdord i] | i < k],
      (* the above line should be the same as using children_from_arity *)
      head_sig t,
      trho rn [::]
    )).

End Runs.

Definition unambiguous (r : nat) (Sigma state : finType)
  (A : tbuta r.+1 Sigma state) (d : Sigma) : Prop :=
  forall (t : tterm r.+1 Sigma) (rho1 rho2 : [r.+1*] -> state),
    wfrun A t d rho1 -> wfrun A t d rho2 -> {in positions t, rho1 =1 rho2}.

Lemma eq_in_map_tuple (T1 : eqType) (T2 : Type) (f1 f2 : T1 -> T2) (k : nat)
      (s : k.-tuple T1) :
   {in s, f1 =1 f2} <->
   [tuple of [seq f1 i | i <- s]] = [tuple of [seq f2 i | i <- s]].
Proof.
  split => [eq1f1f2 | eqt12].
    apply: eq_from_tnth => i; rewrite 2!tnth_map.
    by apply: eq1f1f2; apply: mem_tnth.
  rewrite eq_in_map.
  rewrite -[[seq f1 _ | _ <- _]]/(val [tuple of [seq f1 _ | _ <- _]]).
  rewrite -[[seq f2 _ | _ <- _]]/(val [tuple of [seq f2 _ | _ <- _]]).
  by congr val.
Qed.

Lemma arity_positions (r : nat) (Sigma : finType) (a : Sigma) (k : [r.+2])
    (f : (tterm r.+1 Sigma)^k) :
  arity (positions (tnode a f)) [::] = k.
Proof.
  (*
  rewrite /arity /=.
  case eqordenum : (ord_enum k) => [/=| i w].
    move: eqordenum; rewrite /ord_enum /=.
    case: {+}k; case => [/= i lti | n ltn1 H]; first by apply /eqP.
    exfalso; move: H.
    Opaque pmap.
    rewrite /= -cat1s pmap_cat.
    Transparent pmap.
    rewrite /= /insub /=.
    Search _ pmap cat.
    Search _ cat cons.

    have : iota 0 (Ordinal ltn1) <> [::].
      rewrite /=.


  move: f; case: k; case => [? ? /= | /=]; first by apply /eqP.
  move=> n ltnr f.
  rewrite /ord_enum /=.
  set cs := children _ _.
*)
Admitted.

(*
Fixpoint child_indf (r : nat) (Sigma : finType) (t : tterm r.+1 Sigma)
  (P : [r.+1*] -> Prop)
  (Pleaves : forall l : [r.+1*], l \in positions t -> is_leaf (positions t) l -> P l)
  (Pchildren : forall p : [r.+1*], p \in positions t -> (forall q : [r.+1*],
    (q \in children_from_arity p (arity (positions t) p) -> P q)) -> P p
  )
  (p : [r.+1*]) (pinpos : p \in positions t) : P p :=
  if is_leaf (positionsn t) p as pleaf then
    Pleaf p pinpos pleaf
  else
    Pchildren p pinpos (child_indf r Sigma )
*)


(* TODO remove l \in positions from Pleaves? *)
Lemma child_ind (r : nat) (Sigma : finType)
  (P : [r.+1*] -> Prop) (Q : tterm r.+1 Sigma -> Prop)
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
  (t : tterm r.+1 Sigma) (Qt : Q t) (p : [r.+1*]) (pinpos : p \in positions t) : P p.
Proof.
  move: Qt p pinpos; elim/tterm_nind: t.
    by move=> a Ql p pinpos; apply: (Pleaves (tleaf r.+1 a)).
  move=> a k f IH Qnode p pinpos.
  apply: (Pchildren (tnode a f)) => // q qinchildren.


  /positions_tnode [-> | [j [q [-> qinpos]]]].
    admit.
  have : wdord j :: q \in children_from_arity
  apply: (Pchildren (tnode a f)) => //.
    by rewrite -positions_child.
  move=> s /children_from_arityP [i ->].
  apply: (IH j).
    admit.


  (* TODO no idea how to prove this as such. Maybe with a lemma mapping p \in positions t to t itself? *)
  have [pleaf | notpleaf] := boolP (is_leaf (positions t) p).
    by apply: Pleaves.
  have := Pchildren; apply => // q qinchildren.
Admitted.

Lemma arity_leaf (r : nat) (U : ptree r.+1) (l : [r.+1*]) :
  is_leaf U l -> arity U l = ord0.
Proof.
Admitted.

(* TODO *)
Lemma report_bug X Y (f g : X -> Y) :
  [tuple of map f [tuple]] = [tuple of map g [tuple]].
Proof.
  by rewrite tuple0; symmetry; rewrite tuple0.
Qed.

Lemma children_from_arity0 (r : nat) (p : [r*]) :
  children_from_arity p ord0 = [tuple].
Proof. by rewrite tuple0. Qed.

Lemma arity0 (r : nat) (s : [r.+1*]) :
  arity [:: [::]] s = ord0.
Proof.
  by rewrite /arity /= /is_parent /= andbF.
Qed.

Lemma children_from_arity_positions (r : nat) (Sigma : finType) (t : tterm r.+1 Sigma) (p q : [r.+1*]) :
    p \in positions t ->
    q \in children_from_arity p (arity (positions t) p) ->
  q \in positions t.
Proof.
  elim/tterm_nind: t => [a /= | a k f IH].
    by rewrite arity0 children_from_arity0.
  move=> pinpos /children_from_arityP [i ->].
Admitted.

Lemma unambiguous_deterministic (r : nat) (Sigma state : finType)
  (A : tbuta r.+1 Sigma state) (d : Sigma) :
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

  (*
  elim/tterm_nind => [a /= rho1 rho2 | a m f IH rho1 rho2].
    move=> /wfrunP /= wf1 /wfrunP /= wf2 p pine.
    apply: (deterA ord0 [tuple]).
      have := wf1 p pine; move: pine; rewrite mem_seq1 => /eqP ->.
      by rewrite /arity /= tuple0; apply.
    have := wf2 p pine; move: pine; rewrite mem_seq1 => /eqP ->.
    by rewrite /arity /= tuple0; apply.
  Opaque positions children_from_arity.
  move=> wf1 wf2 /=; elim => [einpos | i q IHp iqinpos].
    apply: deterA.
      by move: wf1 => /wfrunP /(_ [::]) /(_ einpos); apply.
    have := wf2 => /wfrunP /(_ [::]) /(_ einpos); rewrite arity_positions.
    set tup1 := [tuple of [seq rho1 _ | _ <- _]].
    set tup2 := [tuple of [seq rho2 _ | _ <- _]].
    suff -> : tup1 = tup2 by apply.
    rewrite -eq_in_map_tuple => /= p /mapP /= [j _] -> {p}.
    pose rho1' := partial_run rho1 (wdord j).
    pose rho2' := partial_run rho2 (wdord j).
    apply: (IH j rho1' rho2'); last by apply: positions_nil.
      by apply: partial_wfrun; apply: wf1.
    by apply: partial_wfrun; apply: wf2.
  apply: deterA.
    by move: wf1 => /wfrunP /(_ (i :: q)) /(_ iqinpos); apply.
  have := wf2 => /wfrunP /(_ (i :: q)) /(_ iqinpos).
  *)

  (*
  (* FIXME maybe here we want [::] instead of p? But then why is p here? *)
  pose k := arity (positions (tnode a f)) p.
  apply: (deterA k).
    by move: wf1 => /wfrunP /(_ p) /(_ pinpos); apply.
  suff -> : [tuple of map rho1 (children_from_arity p k)] =
            [tuple of map rho2 (children_from_arity p k)].
    by move: wf2 => /wfrunP /(_ p) /(_ pinpos); apply.
  apply: eq_from_tnth => i; rewrite 2!tnth_map.
  Transparent children_from_arity.
  rewrite /children_from_arity tnth_map tnth_ord_tuple.
  apply: IH.
  - admit.
  - admit.
  (* TODO need to see that m = k *)
  (* m is the arity of tnode a f; k is the arity of p *)
  have H := positions_tnode pinpos.
  admit.
  *)
(*
  rewrite /deterministic /unambiguous /=.
  move=> /'forall_'forall_forallP /= deterministicA t rho1 rho2.
  elim/tterm_nind: t => [a /= | a m f IH].
    admit.
  set t := tnode _ _.
  Opaque positions.
  move=> wfr1 wfr2; have := wfr2; have := wfr1.
  move=> /allP /= wf1 /allP /= wf2 p pinpos.
  set k := Ordinal (arity_tree_like p (positions_tree_like t)).
  have /'forall_implyP /= wf1p := wf1 p pinpos.
  have := wf1p k (eq_refl _) => {wf1 wf1p}.
  have /'forall_implyP /= wf2p := wf2 p pinpos.
  have := wf2p k (eq_refl _) => {wf2 wf2p}.
  set rho1c := [tuple of [seq rho1 i | i <- _]] : k.-tuple state.
  set rho2c := [tuple of [seq rho2 i | i <- _]].
  have <- : rho1c = rho2c.
    rewrite {}/rho1c {}/rho2c; apply: eq_from_tnth => j.
    rewrite 2!tnth_map.
    apply: IH; first by apply: wfrun_tnode; apply: wfr1.
      by apply: wfrun_tnode; apply wfr2.
    rewrite /children_from_arity_tuple tnth_map tnth_ord_tuple.
    (* FIXME I think this might not be true *)
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
*)
(*  Transparent positions.*)
Qed.

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
     (s : [r*]) :
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
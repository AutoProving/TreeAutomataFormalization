Set Warnings "-notation-overridden, -notation-incompatible-format".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-format".

Require Import Coq.Program.Wf.

Require Import basic.
Require Import trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Below are old undocumented definitions that might be useful at some point   *)

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

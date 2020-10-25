Set Warnings "-notation-overridden, -notation-incompatible-format".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden, notation-incompatible-format".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rcons_nil (T : eqType) (s : seq T) (x : T) :
  (rcons s x == [::]) = false.
Proof. by case: s. Qed.
Hint Resolve rcons_nil : core.

Lemma addnmBm (n m : nat) : n + m - m = n.
Proof. by rewrite -{2}[m]/(0 + m) subnDr subn0. Qed.

(* TODO pull-request? *)
Lemma leq_bigmax_list (T : eqType) (w : seq T) (F : T -> nat) (j : T) :
    j \in w ->
  F j <= \max_(i <- w) F i.
Proof.
  by move=> /seq_tnthP [n ->]; rewrite big_tnth leq_bigmax.
Qed.

(* TODO pull-request? *)
Lemma sub_in_count (T : eqType) (a1 a2 : pred T) (s : seq T) :
    {in s, subpred a1 a2} ->
  count a1 s <= count a2 s.
Proof.
  move=> ins_sub.
  have filter_mem : filter (mem s) s = s by apply /all_filterP /allP.
  have := count_filter a1 (mem s) s; rewrite filter_mem => ->.
  have := count_filter a2 (mem s) s; rewrite filter_mem => ->.
  apply: sub_count => x /andP [a1x memsx].
  apply /andP; split => //.
  by apply: ins_sub.
Qed.

(* TODO pull-request? *)
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

(* TODO report *)
Lemma report_bug X Y (f g : X -> Y) :
  [tuple of map f [tuple]] = [tuple of map g [tuple]].
Proof.
  by rewrite tuple0; symmetry; rewrite tuple0.
Qed.

Lemma last_headI (T : Type) (x : T) (s : seq T) :
  last (head x s) (behead (rcons s x)) = x.
Proof.
  by case: s => [// | hd tl /=]; rewrite last_rcons.
Qed.

Lemma belast_headI (T : Type) (x : T) (s : seq T) :
  belast (head x s) (behead (rcons s x)) = s.
Proof.
  by case: s => [// | hd tl /=]; rewrite belast_rcons.
Qed.

Lemma eq_mem0c (T : eqType) (x : T) (s : seq T) :
  ~ (nil =i x :: s).
Proof. by move=> /(_ x); rewrite in_nil in_cons eqxx. Qed.

Lemma eq_memc0 (T : eqType) (x : T) (s : seq T) :
  ~ (x :: s =i [::]).
Proof. by move=> /(_ x); rewrite in_nil in_cons eqxx. Qed.

Lemma bigmax_map (T : Type) (s : seq T) (f : T -> nat) :
  \max_(x <- s) f x = \max_(y <- map f s) y.
Proof. by rewrite big_map_id. Qed.

Lemma ordinalE (k : nat) (j : 'I_k) (ltjk : j < k) :
  Ordinal ltjk = j.
Proof. by apply /val_eqP. Qed.

Lemma geq_minlS (m n : nat) : (minn m n).+1 <= m.+1.
Proof. by rewrite -minnSS geq_minl. Qed.

Lemma geq_minrS (m n : nat) : (minn m n).+1 <= n.+1.
Proof. by rewrite -minnSS geq_minr. Qed.

Lemma tnth_zip [S T : eqType] (n : nat) (s : n.-tuple S) (t : n.-tuple T)
    (i : 'I_n) :
  tnth [tuple of zip s t] i = (tnth s i, tnth t i).
Proof.
  rewrite /tnth -nth_zip /=; last by rewrite 2!size_tuple.
  have ltis : i < size [tuple of zip s t].
    by have /eqP -> := (zip_tupleP s t); rewrite ltn_ord.
  by apply: set_nth_default.
Qed.

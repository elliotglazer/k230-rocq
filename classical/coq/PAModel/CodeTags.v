(** The decoder for the exact four-tag named formula encoding. The tag is a
    fixed syntactic numeral; the constructor arguments can be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRTFormula
  Pairing CodeExpressions CodeDescent.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Definition tagged_pair_formula (tag : nat) (a b f : term) : form :=
  ∃ (pair_formula a`[↑] b`[↑] $0 ∧
    f`[↑] == (num 4 ⊗ $0) ⊕ num tag).

Lemma tagged_pair_formula_correct M rho tag a b f :
  holds M rho (tagged_pair_formula tag a b f) <->
  tagged_pair_graph M tag (evalM M rho a) (evalM M rho b) (evalM M rho f).
Proof.
  unfold tagged_pair_formula,tagged_pair_graph. rewrite holds_exists.
  setoid_rewrite holds_and. setoid_rewrite pair_formula_correct.
  unfold holds,evalM. cbn. setoid_rewrite eval_up.
  change ((exists p, pair_graph M (evalM M rho a) (evalM M rho b) p /\
    evalM M rho f = addM M (mulM M (evalM M (p .: rho) (num 4)) p)
      (evalM M (p .: rho) (num tag))) <->
    (exists p, pair_graph M (evalM M rho a) (evalM M rho b) p /\
      evalM M rho f = addM M (mulM M (code_numeral M 4) p) (code_numeral M tag))).
  setoid_rewrite code_eval_num. reflexivity.
Qed.

Lemma tagged_pair_total M tag a b : exists f, tagged_pair_graph M tag a b f.
Proof.
  destruct (pair_total M a b) as [p Hp].
  exists (addM M (mulM M (code_numeral M 4) p) (code_numeral M tag)),p. auto.
Qed.

Lemma tagged_pair_functional M tag a b f g :
  tagged_pair_graph M tag a b f -> tagged_pair_graph M tag a b g -> f=g.
Proof.
  intros [p [Hp ->]] [q [Hq ->]].
  now rewrite (pair_functional M a b p q Hp Hq).
Qed.

Lemma tag_numeral_bound M tag : tag < 4 ->
  coding_lt M (code_numeral M tag) (code_numeral M 4).
Proof.
  intro H. destruct tag as [|[|[|[|tag]]]]; try lia.
  - exists (code_numeral M 3). rewrite coding_add_zero. reflexivity.
  - exists (code_numeral M 2).
    change (succM M (succM M (succM M (succM M (zeroM M)))) =
      succM M (addM M (succM M (zeroM M)) (succM M (succM M (zeroM M))))).
    rewrite !Arithmetic.add_succ, coding_add_zero. reflexivity.
  - exists (code_numeral M 1).
    change (succM M (succM M (succM M (succM M (zeroM M)))) =
      succM M (addM M (succM M (succM M (zeroM M))) (succM M (zeroM M)))).
    rewrite !Arithmetic.add_succ, coding_add_zero. reflexivity.
  - exists (zeroM M). rewrite coding_add_zero_r. reflexivity.
Qed.

Theorem tagged_pair_decode_unique M tag tag' a b a' b' f :
  tag < 4 -> tag' < 4 ->
  tagged_pair_graph M tag a b f -> tagged_pair_graph M tag' a' b' f ->
  tag=tag' /\ a=a' /\ b=b'.
Proof.
  intros Ht Ht' [p [Hp Hf]] [q [Hq Hf']].
  assert (He : addM M (code_numeral M tag) (mulM M p (code_numeral M 4)) =
    addM M (code_numeral M tag') (mulM M q (code_numeral M 4))).
  { rewrite (Arithmetic.add_comm M), (Arithmetic.add_comm M (code_numeral M tag')),
      (mul_comm M p), (mul_comm M q). congruence. }
  destruct (@Peano.iFac_unique (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) (code_numeral M 4)
    p (code_numeral M tag) q (code_numeral M tag')
    (tag_numeral_bound M tag Ht) (tag_numeral_bound M tag' Ht') He) as [Ep Et].
  assert (Etag : tag=tag').
  { apply (@Peano.inu_inj (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H)).
    now rewrite !numeral_inu. }
  subst q. split; [exact Etag|]. exact (pair_injective M p a b a' b' Hp Hq).
Qed.

Print Assumptions tagged_pair_formula_correct.
Print Assumptions tagged_pair_decode_unique.

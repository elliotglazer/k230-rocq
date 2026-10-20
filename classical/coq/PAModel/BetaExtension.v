(** Extension of an internally finite beta-coded sequence in every PA model.
    All lengths, indices, values and codes below range over the model carrier. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Extension.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation one := (S Z).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring extension_model_ring : (model_semiring M).

Lemma coding_le_lt_trans x y z :
  coding_lt M x (S y) -> coding_lt M y z -> coding_lt M x z.
Proof.
  intros Hxy Hyz. destruct (proj1 (coding_lt_succ_cases M x y) Hxy) as [Hlt | ->].
  - eapply coding_lt_trans; eassumption.
  - exact Hyz.
Qed.

Lemma coding_le_add x y : coding_lt M x (S (x+y)).
Proof. exists y. reflexivity. Qed.

Lemma scaled_common_multiple n bound :
  exists c, positive_common_multiple M n c /\ coding_lt M bound c.
Proof.
  destruct (positive_common_multiple_total M n) as [c [Hc Hdiv]].
  exists (c*(S bound)). split.
  - split.
    + apply positive_product; [exact Hc|apply coding_zero_lt_succ].
    + intros d Hd. destruct (Hdiv d Hd) as [k Hk].
      exists (k*(S bound)). rewrite Hk. ring.
  - destruct Hc as [a Ha]. rewrite (Arithmetic.add_zero M a) in Ha.
    rewrite Ha. exists (a*(S bound)).
    rewrite (Arithmetic.mul_succ M a (S bound)), (Arithmetic.add_succ M bound (a*(S bound))).
    reflexivity.
Qed.

Lemma remainder_le_dividend b q r :
  remainder M b q r -> coding_lt M r (S b).
Proof.
  intros [_ [d Hd]]. exists (d*q). rewrite Hd. f_equal. ring.
Qed.

Lemma modulus_above_scale c i : coding_lt M c (beta_modulus M c i).
Proof.
  unfold beta_modulus. exists (i*c). rewrite (Arithmetic.mul_succ M i c). reflexivity.
Qed.

(** Parameters after the two argument slots are n,x,b,c respectively. *)
Definition extension_relation_formula : form :=
  (($1 == $2 ∧ $0 == $3) ∨
   (($1 == $2 → ⊥) ∧ beta_formula $4 $5 $1 $0)).

Lemma extension_relation_correct rho n x b c j r :
  holds M (r .: j .: n .: x .: b .: c .: rho) extension_relation_formula <->
    ((j=n /\ r=x) \/ (j<>n /\ beta M b c j r)).
Proof.
  unfold extension_relation_formula.
  change (((j=n /\ r=x) \/
    (j<>n /\ holds M (r .: j .: n .: x .: b .: c .: rho)
      (beta_formula $4 $5 $1 $0))) <->
      ((j=n /\ r=x) \/ (j<>n /\ beta M b c j r))).
  rewrite beta_formula_correct. reflexivity.
Qed.

Theorem beta_extension b c n x :
  exists b' c',
    (forall i r, coding_lt M i n -> beta M b c i r -> beta M b' c' i r) /\
    beta M b' c' n x.
Proof.
  destruct (scaled_common_multiple (S n) (b+x)) as [c' [Hcm Hbound]].
  assert (Hbc : coding_lt M b c').
  { apply (coding_le_lt_trans b (b+x) c'); [apply coding_le_add|exact Hbound]. }
  assert (Hxc : coding_lt M x c').
  { apply (coding_le_lt_trans x (b+x) c'); [|exact Hbound].
    replace (b+x) with (x+b) by ring. apply coding_le_add. }
  set (rho := n .: x .: b .: c .: (fun _ => Z)).
  assert (Htotal : forall j, coding_lt M j (S n) ->
    exists r, holds M (r .: j .: rho) extension_relation_formula).
  { intros j Hj.
    destruct (@Peano.D_eq_dec D (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) j n) as [Heq|Hne].
    - exists x. unfold rho. apply extension_relation_correct. left. auto.
    - destruct (beta_total M b c j) as [r Hr].
      exists r. unfold rho. apply extension_relation_correct. right. auto. }
  assert (Hpair : forall i j, coding_lt M i j -> coding_lt M j (S n) ->
    unit_modulo M (beta_modulus M c' i) (beta_modulus M c' j)).
  { intros i j Hij Hjn. apply (beta_units_from_common_multiple M (S n) c' Hcm i j Hij).
    apply coding_lt_succ_cases. left. exact Hjn. }
  destruct (crt_for_formula M rho extension_relation_formula c' (S n) Htotal Hpair)
    as [b' Hb].
  exists b',c'. split.
  - intros i r Hin Hr.
    assert (Hin' : coding_lt M i (S n)) by
      (apply coding_lt_succ_cases;left;exact Hin).
    destruct (Hb i Hin') as [s [Hs Hbs]].
    unfold rho in Hs. apply extension_relation_correct in Hs.
    destruct Hs as [[Heq _]|[Hne Hs]].
    + exfalso. exact (@Peano.lt_neq D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i n Hin Heq).
    + assert (s=r) by (eapply beta_unique; eassumption). subst s.
      apply congruent_remainder; [apply coding_zero_lt_succ| |exact Hbs].
      apply (coding_lt_trans M r c' (beta_modulus M c' i)).
      * apply (coding_le_lt_trans r b c'); [apply (remainder_le_dividend b (beta_modulus M c i) r Hr)|exact Hbc].
      * apply modulus_above_scale.
  - destruct (Hb n (coding_lt_succ M n)) as [r [Hr Hbr]].
    unfold rho in Hr. apply extension_relation_correct in Hr.
    destruct Hr as [[_ Heq]|[Hne _]]; [subst r|contradiction].
    apply congruent_remainder; [apply coding_zero_lt_succ| |exact Hbr].
    apply (coding_lt_trans M x c' (beta_modulus M c' n));
      [exact Hxc|apply modulus_above_scale].
Qed.

End Extension.

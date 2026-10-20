(** Hygiene for rebasing an arbitrary internal quotation. Free names may be
    below or above the allocation interval, but cannot occur inside it. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs NumericalEnvironments
  QuotationHygiene QuotationAllocationBounds QuotationNamedSubstitution
  SubstitutionEnvironmentTotal.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_rebase_hygiene M source b c n k domain :=
  quotation_allocation_avoids M source k (zeroM M) /\
  quotation_allocation_avoids M source k domain /\
  forall i x,environment_lookup M b c n i x -> quotation_allocation_avoids M source k x.

Definition quotation_rebase_hygiene_formula (source b c n k domain : term) : form :=
  quotation_allocation_avoids_formula source k zero ∧
  (quotation_allocation_avoids_formula source k domain ∧
   ∀∀ (environment_lookup_formula (code_lift2 b) (code_lift2 c) (code_lift2 n) $1 $0 →
     quotation_allocation_avoids_formula (code_lift2 source) (code_lift2 k) $0)).
Local Opaque holds quotation_allocation_avoids_formula environment_lookup_formula.
Lemma quotation_rebase_hygiene_correct M rho source b c n k domain :
  holds M rho (quotation_rebase_hygiene_formula source b c n k domain) <->
  quotation_rebase_hygiene M (evalM M rho source) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho domain).
Proof.
  unfold quotation_rebase_hygiene_formula,quotation_rebase_hygiene.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite quotation_allocation_avoids_correct.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Lemma quotation_allocation_below M source k y :
  coding_lt M y k -> quotation_allocation_avoids M source k y.
Proof.
  intros Hy d Hd E.
  assert (Hlt : coding_lt M y (addM M k d)).
  { apply (@Peano.lt_le_trans (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) y (addM M k d) k Hy).
    exists d. reflexivity. }
  rewrite E in Hlt.
  exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) y y Hlt eq_refl).
Qed.

Theorem quotation_safe_rebase_hygiene M source b c n k domain :
  quotation_safe M b c n k domain -> quotation_rebase_hygiene M source b c n k domain.
Proof.
  intros [HD HE]. split.
  - apply quotation_allocation_below. exact (environment_below_zero M b c n k HE).
  - split;[now apply quotation_allocation_below|].
    intros i x HX. apply quotation_allocation_below. exact (HE i x HX).
Qed.

Lemma quotation_rebase_hygiene_subformula M a source b c n k domain :
  coding_lt M a source -> quotation_rebase_hygiene M source b c n k domain ->
  quotation_rebase_hygiene M a b c n k domain.
Proof.
  intros Ha [HZ [HD HE]]. split.
  - exact (quotation_allocation_subformula M a source k (zeroM M) Ha HZ).
  - split;[exact (quotation_allocation_subformula M a source k domain Ha HD)|].
    intros i x HX. exact (quotation_allocation_subformula M a source k x Ha (HE i x HX)).
Qed.

Lemma quotation_rebase_hygiene_child M a source b c n k domain y d e m :
  coding_lt M a source -> quotation_rebase_hygiene M source b c n k domain ->
  quotation_allocation_avoids M a (succM M k) y ->
  environment_cons M b c n y d e m ->
  quotation_rebase_hygiene M a d e m (succM M k) domain.
Proof.
  intros Ha [HZ [HD HE]] HY HC. split.
  - exact (quotation_allocation_child M a source k (zeroM M) Ha HZ).
  - split;[exact (quotation_allocation_child M a source k domain Ha HD)|].
    intros i x HX.
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [E|[j E]];subst i.
    + apply (proj1 (environment_cons_head M b c n y d e m x HC)) in HX. now subst x.
    + apply (proj1 (environment_cons_tail M b c n y d e m j x HC)) in HX.
      exact (quotation_allocation_child M a source k x Ha (HE j x HX)).
Qed.

Lemma rebase_environment_head_replace M source b c n k domain d e m y d' e' m' :
  quotation_rebase_hygiene M source b c n k domain ->
  environment_cons M b c n k d e m -> environment_cons M b c n y d' e' m' ->
  environment_named_replace M d e m d' e' m' k y.
Proof.
  intros [_ [_ HE]] HC HC' i a a' HA HA'.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M b c n k d e m a HC)) in HA.
    apply (proj1 (environment_cons_head M b c n y d' e' m' a' HC')) in HA'.
    subst a a'. left;auto.
  - apply (proj1 (environment_cons_tail M b c n k d e m j a HC)) in HA.
    apply (proj1 (environment_cons_tail M b c n y d' e' m' j a' HC')) in HA'.
    assert (a'=a) by exact (environment_lookup_functional M b c n j a' a HA' HA).
    subst a'. right. split;[|reflexivity].
    intro E. apply (quotation_allocation_head M source k a (HE j a HA)). symmetry. exact E.
Qed.

Section CommonFresh.
Variable M : Model.
Add Ring quotation_rebase_ring : (model_semiring M).

Lemma quotation_common_fresh source k l v w domain :
  exists y,coding_lt M v y /\ coding_lt M w y /\ coding_lt M domain y /\
    coding_lt M k y /\ coding_lt M l y /\
    quotation_allocation_avoids M source k y /\ quotation_allocation_avoids M source l y.
Proof.
  set (cap:=addM M source (code_numeral M quotation_allocation_margin)).
  set (y:=succM M (addM M (addM M (addM M v w) domain) (addM M (addM M k l) cap))).
  exists y. split.
  - exists (addM M (addM M w domain) (addM M (addM M k l) cap)). unfold y. f_equal. ring.
  - split.
    + exists (addM M (addM M v domain) (addM M (addM M k l) cap)). unfold y. f_equal. ring.
    + split.
      * exists (addM M (addM M v w) (addM M (addM M k l) cap)). unfold y. f_equal. ring.
      * split.
        -- exists (addM M (addM M (addM M v w) domain) (addM M l cap)). unfold y. f_equal. ring.
        -- split.
           ++ exists (addM M (addM M (addM M v w) domain) (addM M k cap)). unfold y. f_equal. ring.
           ++ split;intros d [u HU] E.
              ** assert (Hlt : coding_lt M (addM M k d) y).
                 { exists (addM M (addM M (addM M v w) domain) (addM M l (succM M u))).
                   unfold y. change (cap=succM M (addM M d u)) in HU. rewrite HU.
                   f_equal. rewrite (succ_as_add M (addM M d u)),(succ_as_add M u). ring. }
                 rewrite E in Hlt. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
                   (fun ax H rho=>axioms M ax rho H) y y Hlt eq_refl).
              ** assert (Hlt : coding_lt M (addM M l d) y).
                 { exists (addM M (addM M (addM M v w) domain) (addM M k (succM M u))).
                   unfold y. change (cap=succM M (addM M d u)) in HU. rewrite HU.
                   f_equal. rewrite (succ_as_add M (addM M d u)),(succ_as_add M u). ring. }
                 rewrite E in Hlt. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
                   (fun ax H rho=>axioms M ax rho H) y y Hlt eq_refl).
Qed.
End CommonFresh.

Print Assumptions quotation_rebase_hygiene_correct.
Print Assumptions quotation_common_fresh.

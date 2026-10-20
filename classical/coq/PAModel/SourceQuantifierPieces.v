(** Internal access to quantified bodies, with the pcs context bound.
    Access traces and source codes may be nonstandard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded NumericalTraces SourceQuantifierPieceRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_quantifier_body M f n k a := exists r,
  qpiece_record M f n k a r /\ trace_derives M qpiece_rules r.
Definition source_quantifier_body_formula (f n k a:term) : form :=
  ∃ (qpiece_record_formula f`[↑] n`[↑] k`[↑] a`[↑] $0 ∧ trace_derives_formula qpiece_rules $0).
Local Opaque holds qpiece_record_formula trace_derives_formula.

Theorem source_quantifier_body_formula_correct M rho f n k a :
  holds M rho (source_quantifier_body_formula f n k a) <->
  source_quantifier_body M (evalM M rho f) (evalM M rho n) (evalM M rho k) (evalM M rho a).
Proof.
  unfold source_quantifier_body_formula,source_quantifier_body.
  setoid_rewrite holds_ex. setoid_rewrite holds_and. setoid_rewrite qpiece_record_formula_correct.
  setoid_rewrite trace_derives_formula_correct. unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_quantifier_body_top M f n a : qpiece_quantifier M f a ->
  source_quantifier_body M f n n a.
Proof.
  intro H. destruct (qpiece_record_total M f n n a) as [r HR]. exists r. split;[exact HR|].
  apply trace_derives_base,qpiece_rule_base. exists f,n,a. auto.
Qed.
Theorem source_quantifier_body_child M f n child childn k a :
  qpiece_child M f n child childn -> source_quantifier_body M child childn k a ->
  source_quantifier_body M f n k a.
Proof.
  intros HC [p [HP HD]]. destruct (qpiece_record_total M f n k a) as [r HR]. exists r.
  split;[exact HR|]. apply (trace_derives_unary M qpiece_rules r p HD),qpiece_rule_unary.
  exists f,n,k,a,child,childn. auto.
Qed.

Theorem source_quantifier_body_cases M f n k a : source_quantifier_body M f n k a ->
  (k=n /\ qpiece_quantifier M f a) \/
  exists child childn,qpiece_child M f n child childn /\ source_quantifier_body M child childn k a.
Proof.
  intros [r [HR HD]]. destruct (trace_derives_inv M qpiece_rules r HD)
    as [HB|[[p [HP HU]]|[p [q [HP [HQ HB]]]]]].
  - apply qpiece_rule_base in HB. destruct HB as (f' & n' & a' & HR' & HQ).
    destruct (qpiece_record_injective M f n k a f' n' n' a' r HR HR') as [HF [HN [HK HA]]].
    subst f' n' a' k. now left.
  - apply qpiece_rule_unary in HU. destruct HU as (f' & n' & k' & a' & child & childn & HR' & HC & HS).
    destruct (qpiece_record_injective M f n k a f' n' k' a' r HR HR') as [HF [HN [HK HA]]].
    subst f' n' k' a'. right. exists child,childn. split;[exact HS|]. exists p. auto.
  - exfalso. exact (qpiece_rule_binary M r p q HB).
Qed.

Definition qpiece_bounded_row M r := forall f n k a,
  qpiece_record M f n k a r -> source_bounded M f n -> source_bounded M a (succM M k).
Definition qpiece_bounded_row_formula : form :=
  ∀∀∀∀ (qpiece_record_formula $3 $2 $1 $0 $4 →
    source_bounded_accept_formula $3 $2 → source_bounded_accept_formula $0 (σ $1)).
Local Opaque source_bounded_accept_formula.
Lemma qpiece_bounded_row_definable M : Definable1 M (qpiece_bounded_row M).
Proof.
  exists qpiece_bounded_row_formula,(fun _=>zeroM M). intro r.
  unfold qpiece_bounded_row_formula,qpiece_bounded_row.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite qpiece_record_formula_correct. setoid_rewrite source_bounded_accept_formula_correct.
  reflexivity.
Qed.

Theorem source_quantifier_body_bounded M f n k a :
  source_quantifier_body M f n k a -> source_bounded M f n -> source_bounded M a (succM M k).
Proof.
  intros [r [HR HD]] HF.
  assert (HBound:forall r,trace_derives M qpiece_rules r -> qpiece_bounded_row M r).
  { clear f n k a r HR HD HF. apply (trace_derives_induction M qpiece_rules (qpiece_bounded_row M)).
    - apply qpiece_bounded_row_definable.
    - intros r HB f' n' k' a' HR' HF'. apply qpiece_rule_base in HB.
      destruct HB as (f & n & a & HR & HQ).
      destruct (qpiece_record_injective M f n n a f' n' k' a' r HR HR') as [EF [EN [EK EA]]].
      subst f' n' k' a'. destruct HQ as [HQ|HQ].
      + exact (proj1 (source_bounded_accept_unary M SFAll a f n (or_introl eq_refl) HQ) HF').
      + exact (proj1 (source_bounded_accept_unary M SFEx a f n (or_intror eq_refl) HQ) HF').
    - intros r p IH HU f' n' k' a' HR' HF'. apply qpiece_rule_unary in HU.
      destruct HU as (f & n & k & a & child & childn & HR & HC & HS).
      destruct (qpiece_record_injective M f n k a f' n' k' a' r HR HR') as [EF [EN [EK EA]]].
      subst f' n' k' a'. exact (IH child childn k a HC (qpiece_child_bounded M f n child childn HF' HS)).
    - intros r p q HP HQ HB. exfalso. exact (qpiece_rule_binary M r p q HB). }
  exact (HBound r HD f n k a HR HF).
Qed.

Print Assumptions source_quantifier_body_formula_correct.
Print Assumptions source_quantifier_body_top.
Print Assumptions source_quantifier_body_child.
Print Assumptions source_quantifier_body_cases.
Print Assumptions source_quantifier_body_bounded.

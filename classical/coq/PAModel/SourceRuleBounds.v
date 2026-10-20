(** Bounds for the instantiation terms selected in internally finite source
    proofs. These terms need not occur in the conclusion formula. Keeping
    their witnesses is necessary when constructing one quotation environment.
    This does not yet translate quantified proofs into K. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs NumericalTraces NumericalContexts
  NumericalInstantiation SourceSequents SourcePropositionalRules
  SourceQuantifierRules SetFormulaCodes SourceBoundMonotone BoundedCollection SentenceBounds
  SourceTraceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_AllE_at M r p k := exists b c n a f t g,
  (source_sequent M b c n g r /\ source_sequent M b c n f p /\
    sf_relation M SFAll a (zeroM M) f /\ numerical_instantiation M a t g) /\
  coding_lt M t k.
Definition source_ExI_at M r p k := exists b c n a f t g,
  (source_sequent M b c n f r /\ source_sequent M b c n g p /\
    sf_relation M SFEx a (zeroM M) f /\ numerical_instantiation M a t g) /\
  coding_lt M t k.

Definition source_AllE_at_formula : form := ∃∃∃∃∃∃∃
  ((source_sequent_formula $6 $5 $4 $0 $7 ∧
    (source_sequent_formula $6 $5 $4 $2 $8 ∧
    (sf_formula SFAll $3 zero $2 ∧ numerical_instantiation_formula $3 $1 $0))) ∧
    Peano.sless $1 $9).
Definition source_ExI_at_formula : form := ∃∃∃∃∃∃∃
  ((source_sequent_formula $6 $5 $4 $2 $7 ∧
    (source_sequent_formula $6 $5 $4 $0 $8 ∧
    (sf_formula SFEx $3 zero $2 ∧ numerical_instantiation_formula $3 $1 $0))) ∧
    Peano.sless $1 $9).

Local Opaque holds source_sequent_formula sf_formula numerical_instantiation_formula
  source_prop_unary_formula source_row_wf_formula source_case_AllI_formula
  Peano.sless.
Lemma source_AllE_at_correct M rho r p k :
  holds M (r .: p .: k .: rho) source_AllE_at_formula <-> source_AllE_at M r p k.
Proof.
  unfold source_AllE_at_formula,source_AllE_at.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct.
  setoid_rewrite less_formula_correct. reflexivity.
Qed.
Lemma source_ExI_at_correct M rho r p k :
  holds M (r .: p .: k .: rho) source_ExI_at_formula <-> source_ExI_at M r p k.
Proof.
  unfold source_ExI_at_formula,source_ExI_at.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct.
  setoid_rewrite less_formula_correct. reflexivity.
Qed.

Definition source_unary_at M r p k := source_prop_unary M r p \/
  (source_row_wf M r /\
    (source_case_AllI M r p \/ source_AllE_at M r p k \/ source_ExI_at M r p k)).
Definition source_unary_at_formula : form := source_prop_unary_formula ∨
  (source_row_wf_formula $0 ∧
    (source_case_AllI_formula ∨ (source_AllE_at_formula ∨ source_ExI_at_formula))).

Local Opaque source_AllE_at_formula source_ExI_at_formula.
Lemma source_unary_at_correct M rho r p k :
  holds M (r .: p .: k .: rho) source_unary_at_formula <-> source_unary_at M r p k.
Proof.
  unfold source_unary_at_formula,source_unary_at.
  rewrite holds_or,holds_and. repeat setoid_rewrite holds_or.
  rewrite source_prop_unary_correct,source_row_wf_formula_correct,
    source_case_AllI_correct,source_AllE_at_correct,source_ExI_at_correct.
  reflexivity.
Qed.
Lemma source_unary_at_bound : bounded 3 source_unary_at_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Lemma source_unary_has_bound M r p :
  source_full_unary M r p -> exists k, source_unary_at M r p k.
Proof.
  intros [H|[Hw [H|[H|H]]]].
  - exists (zeroM M). now left.
  - exists (zeroM M). right. split;[exact Hw|now left].
  - destruct H as [b [c [n [a [f [t [g H]]]]]]].
    exists (succM M t). right. split;[exact Hw|]. right;left.
    exists b,c,n,a,f,t,g. split;[exact H|apply coding_lt_succ].
  - destruct H as [b [c [n [a [f [t [g H]]]]]]].
    exists (succM M t). right. split;[exact Hw|]. right;right.
    exists b,c,n,a,f,t,g. split;[exact H|apply coding_lt_succ].
Qed.
Lemma source_unary_at_monotone M r p k l :
  source_unary_at M r p k -> coding_lt M k (succM M l) -> source_unary_at M r p l.
Proof.
  intros [H|[Hw [H|[H|H]]]] Hkl.
  - now left.
  - right. split;[exact Hw|now left].
  - right. split;[exact Hw|]. right;left.
    destruct H as [b [c [n [a [f [t [g [H Ht]]]]]]]].
    exists b,c,n,a,f,t,g. split;[exact H|]. exact (source_bound_lt_le M t k l Ht Hkl).
  - right. split;[exact Hw|]. right;right.
    destruct H as [b [c [n [a [f [t [g [H Ht]]]]]]]].
    exists b,c,n,a,f,t,g. split;[exact H|]. exact (source_bound_lt_le M t k l Ht Hkl).
Qed.
Lemma source_unary_at_forget M r p k : source_unary_at M r p k -> source_full_unary M r p.
Proof.
  intros [H|[Hw [H|[H|H]]]].
  - now left.
  - right. split;[exact Hw|now left].
  - right. split;[exact Hw|]. right;left.
    destruct H as [b [c [n [a [f [t [g [H _]]]]]]]]. now exists b,c,n,a,f,t,g.
  - right. split;[exact Hw|]. right;right.
    destruct H as [b [c [n [a [f [t [g [H _]]]]]]]]. now exists b,c,n,a,f,t,g.
Qed.

Definition source_unary_at_instance (r p k : term) : form :=
  source_unary_at_formula[r .: p .: k..].
Local Transparent holds.
Lemma source_unary_at_instance_correct M rho r p k :
  holds M rho (source_unary_at_instance r p k) <->
  source_unary_at M (evalM M rho r) (evalM M rho p) (evalM M rho k).
Proof.
  unfold source_unary_at_instance.
  rewrite <- (source_unary_at_correct M (fun _ => zeroM M)).
  unfold holds. rewrite sat_comp.
  apply (bound_ext _ source_unary_at_bound).
  intros [|[|[|i]]] Hi;try reflexivity;lia.
Qed.

Definition source_justified_at M b c i r k :=
  trace_base M source_full_rules r \/
  (exists j p, coding_lt M j i /\ beta M b c j p /\ source_unary_at M r p k) \/
  (exists j h p q, coding_lt M j i /\ coding_lt M h i /\
    beta M b c j p /\ beta M b c h q /\ trace_binary M source_full_rules r p q).
Definition source_justified_at_formula (b c i r k : term) : form :=
  trace_base_instance source_full_rules r ∨
  ((∃∃ (Peano.sless $1 (code_lift2 i) ∧
    (beta_formula (code_lift2 b) (code_lift2 c) $1 $0 ∧
    source_unary_at_instance (code_lift2 r) $0 (code_lift2 k)))) ∨
   (∃∃∃∃ (Peano.sless $3 (lift4 i) ∧ (Peano.sless $2 (lift4 i) ∧
    (beta_formula (lift4 b) (lift4 c) $3 $1 ∧
    (beta_formula (lift4 b) (lift4 c) $2 $0 ∧
    trace_binary_instance source_full_rules (lift4 r) $1 $0)))))).

Local Opaque holds trace_base_instance source_unary_at_instance trace_binary_instance beta_formula.
Lemma source_justified_at_correct M rho b c i r k :
  holds M rho (source_justified_at_formula b c i r k) <->
  source_justified_at M (evalM M rho b) (evalM M rho c) (evalM M rho i)
    (evalM M rho r) (evalM M rho k).
Proof.
  unfold source_justified_at_formula,source_justified_at.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  rewrite trace_base_instance_correct. setoid_rewrite source_unary_at_instance_correct.
  setoid_rewrite trace_binary_instance_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite beta_formula_correct.
  repeat setoid_rewrite code_eval_lift2. try setoid_rewrite lift4_correct.
  reflexivity.
Qed.
Lemma source_justified_has_bound M b c i r :
  trace_justified M source_full_rules b c i r -> exists k,source_justified_at M b c i r k.
Proof.
  intros [H|[H|H]].
  - exists (zeroM M). now left.
  - destruct H as [j [p [Hj [Hp Hu]]]]. apply source_full_trace_unary in Hu.
    destruct (source_unary_has_bound M r p Hu) as [k Hk].
    exists k. right;left. now exists j,p.
  - exists (zeroM M). right;right. exact H.
Qed.
Lemma source_justified_at_monotone M b c i r k l :
  source_justified_at M b c i r k -> coding_lt M k (succM M l) ->
  source_justified_at M b c i r l.
Proof.
  intros [H|[H|H]] Hkl.
  - now left.
  - right;left. destruct H as [j [p [Hj [Hp Hu]]]]. exists j,p.
    split;[exact Hj|]. split;[exact Hp|].
    exact (source_unary_at_monotone M r p k l Hu Hkl).
  - now right;right.
Qed.

Lemma source_justified_at_forget M b c i r k :
  source_justified_at M b c i r k -> trace_justified M source_full_rules b c i r.
Proof.
  intros [H|[H|H]].
  - now left.
  - right;left. destruct H as [j [p [Hj [Hp Hu]]]]. exists j,p.
    split;[exact Hj|]. split;[exact Hp|]. apply source_full_trace_unary.
    exact (source_unary_at_forget M r p k Hu).
  - now right;right.
Qed.

Definition source_rule_bound_witness_formula : form :=
  ∃ (beta_formula $3 $4 $2 $0 ∧ source_justified_at_formula $3 $4 $2 $0 $1).
Local Opaque source_justified_at_formula.
Lemma source_rule_bound_witness_correct M b c i k :
  holds M (k .: i .: b .: c .: fun _ => zeroM M) source_rule_bound_witness_formula <->
  exists r,beta M b c i r /\ source_justified_at M b c i r k.
Proof.
  unfold source_rule_bound_witness_formula.
  rewrite holds_ex. setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
  setoid_rewrite source_justified_at_correct. reflexivity.
Qed.

Theorem source_trace_instantiation_bound M b c n :
  trace_sequence M source_full_rules b c n ->
  exists bound,forall i r,coding_lt M i n -> beta M b c i r ->
    source_justified_at M b c i r bound.
Proof.
  intro HS.
  assert (HT : forall i,coding_lt M i n -> exists k,
    holds M (k .: i .: b .: c .: fun _ => zeroM M) source_rule_bound_witness_formula).
  { intros i Hi. destruct (beta_total M b c i) as [r Hr].
    destruct (source_justified_has_bound M b c i r (HS i r Hi Hr)) as [k Hk].
    exists k. apply source_rule_bound_witness_correct. now exists r. }
  destruct (bounded_collection M source_rule_bound_witness_formula
    (b .: c .: fun _ => zeroM M) n HT) as [bound HB].
  exists bound. intros i r Hi Hr. destruct (HB i Hi) as [k [Hkb Hk]].
  apply source_rule_bound_witness_correct in Hk as [r' [Hr' Hk]].
  assert (r'=r) by exact (beta_unique M b c i r' r Hr' Hr). subst r'.
  apply (source_justified_at_monotone M b c i r k bound Hk).
  apply coding_lt_succ_cases. now left.
Qed.

Theorem source_trace_uniform_bound M b c n :
  trace_sequence M source_full_rules b c n ->
  exists bound,forall i r,coding_lt M i n -> beta M b c i r ->
    source_row_at_bound M r bound /\ source_justified_at M b c i r bound.
Proof.
  intro HS.
  destruct (source_trace_common_bound M b c n HS) as [f HF].
  destruct (source_trace_instantiation_bound M b c n HS) as [t HT].
  assert (HU : exists k,coding_lt M f (succM M k) /\ coding_lt M t (succM M k)).
  { destruct (@Peano.trichotomy (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) f t) as [Hft|[E|Htf]].
    - exists t. split;[apply coding_lt_succ_cases;now left|apply coding_lt_succ].
    - subst t. exists f. split;apply coding_lt_succ.
    - exists f. split;[apply coding_lt_succ|apply coding_lt_succ_cases;now left]. }
  destruct HU as [bound [Hf Ht]]. exists bound. intros i r Hi Hr. split.
  - exact (source_row_at_bound_monotone M r f bound (HF i r Hi Hr) Hf).
  - exact (source_justified_at_monotone M b c i r t bound (HT i r Hi Hr) Ht).
Qed.

Print Assumptions source_unary_at_correct.
Print Assumptions source_justified_at_correct.
Print Assumptions source_trace_instantiation_bound.
Print Assumptions source_trace_uniform_bound.

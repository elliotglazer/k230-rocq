(** Initial environments for a bounded source proof. All live free variables
    may share one target name. The out-of-range zero entry is not included
    among the live domain assumptions. Quantifier rules still have to be
    transported under the environments obtained by prepending fresh names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions CodeDescent CodeTags NumericalProofs NumericalEnvironments
  NumericalContexts NumericalTraces SourceQuantifierRules SourceTraceBounds SourceRuleBounds
  BoundedCollection QuotationHygiene LiveDomainContexts DomainContexts.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition constant_environment M b c n x :=
  forall i y,coding_lt M i n -> beta M b c i y -> y=x.

Theorem constant_environment_total M n x :
  exists b c,constant_environment M b c n x.
Proof.
  destruct (bounded_collection_table M ($0 == $2)
    (x .: fun _ => zeroM M) n) as [b [c H]].
  - intros i Hi. exists x. reflexivity.
  - exists b,c. intros i y Hi Hy. exact (H i y Hi Hy).
Qed.

Lemma constant_environment_lookup M b c n x i y :
  constant_environment M b c n x -> coding_lt M i n ->
  environment_lookup M b c n i y -> y=x.
Proof.
  intros HC Hi Hy. apply (HC i y Hi).
  exact (proj1 (environment_lookup_inside M b c n i y Hi) Hy).
Qed.

Lemma constant_environment_value M b c n x i :
  constant_environment M b c n x -> coding_lt M i n ->
  environment_lookup M b c n i x.
Proof.
  intros HC Hi. destruct (environment_lookup_total M b c n i) as [y Hy].
  pose proof (constant_environment_lookup M b c n x i y HC Hi Hy) as E.
  now subst y.
Qed.

Theorem constant_environment_safe M b c n x fresh domain :
  constant_environment M b c n x -> coding_lt M x fresh ->
  coding_lt M (zeroM M) fresh -> coding_lt M domain fresh ->
  quotation_safe M b c n fresh domain.
Proof.
  intros HC Hx Hzero Hdomain. split;[exact Hdomain|].
  intros i y Hy. destruct (environment_lt_cases M i n) as [Hi|Hi].
  - now rewrite (constant_environment_lookup M b c n x i y HC Hi Hy).
  - apply (proj1 (environment_lookup_outside M b c n i y Hi)) in Hy.
    now subst y.
Qed.

Theorem constant_live_context_member M b c n x domain d e f :
  constant_environment M b c n x -> live_domain_context M b c n domain d e ->
  context_member M d e n f -> membership_graph M domain x f.
Proof.
  intros HC HD HF.
  apply (proj1 (live_domain_context_member_exact M b c n domain d e f HD)) in HF.
  destruct HF as [i [y [Hi [Hy Hf]]]].
  pose proof (constant_environment_lookup M b c n x i y HC Hi Hy) as E.
  now subst y.
Qed.

Theorem constant_live_context_exact M b c n x domain d e f :
  constant_environment M b c n x -> live_domain_context M b c n domain d e ->
  coding_lt M (zeroM M) n ->
  (context_member M d e n f <-> membership_graph M domain x f).
Proof.
  intros HC HD Hn. split.
  - exact (constant_live_context_member M b c n x domain d e f HC HD).
  - intro Hf. apply (proj2 (live_domain_context_member_exact M b c n domain d e f HD)).
    exists (zeroM M),x. split;[exact Hn|]. split;[|exact Hf].
    exact (constant_environment_value M b c n x (zeroM M) HC Hn).
Qed.

Theorem source_trace_initial_environment M b c n :
  trace_sequence M source_full_rules b c n ->
  exists bound eb ec,
    constant_environment M eb ec bound (succM M (zeroM M)) /\
    quotation_safe M eb ec bound (succM M (succM M (zeroM M))) (zeroM M) /\
    forall i r,coding_lt M i n -> beta M b c i r ->
      source_row_at_bound M r bound /\ source_justified_at M b c i r bound.
Proof.
  intro HS. destruct (source_trace_uniform_bound M b c n HS) as [bound HB].
  destruct (constant_environment_total M bound (succM M (zeroM M))) as [eb [ec HE]].
  exists bound,eb,ec. split;[exact HE|]. split;[|exact HB].
  apply (constant_environment_safe M eb ec bound (succM M (zeroM M))
    (succM M (succM M (zeroM M))) (zeroM M) HE).
  - apply coding_lt_succ.
  - apply coding_zero_lt_succ.
  - apply coding_zero_lt_succ.
Qed.

Print Assumptions constant_environment_total.
Print Assumptions constant_live_context_exact.
Print Assumptions source_trace_initial_environment.

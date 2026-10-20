(** Discharge the two ordinary totality/monotonicity assumptions and
    obtain an actual ZFR theorem. Syntax bounds alone remain explicit. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull
  SourceProofWeakening SourceLeastOrdinalWitness SourceSetTheoryDescriptors SourceDescriptorProvability
  SourceFiniteProofContexts SourceZFRProvability SourceOrdinalInitialTotality SourceOrdinalInitialMonotonicity
  SourceOrdinalCoverageSyntax SourceOrdinalCollectionPlan SourceOrdinalCollectionInContext.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_ordinal_collection_theorem_bounded M phi total mono output tail implication count bound :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_initial_totality_graph M phi total ->source_oc_initial_monotonicity_graph M phi mono ->
  source_oc_output_graph M phi (code_numeral M 1) output ->
  source_bounded M total bound ->source_bounded M mono bound ->
  sf_relation M SFImpl mono output tail ->sf_relation M SFImpl total tail implication ->
  source_zfr_provable M implication.
Proof.
  intros HB HT HM HO HTB HMB HTail HImp.
  destruct (source_oc_collection_plan_total M phi total mono output count HB HT HM HO)
    as (envelope&leastDouble&HPlan&PEnvelope&PDouble).
  assert (Premises:forall f,In f [envelope;leastDouble] ->
    source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f [<-|[<-|[]]];apply (proj2 (source_zfr_descriptor_provable M _));assumption. }
  destruct (source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises)
    as (b&c&n&HContext&P).
  pose proof (P envelope (or_introl eq_refl)) as PE.
  pose proof (P leastDouble (or_intror (or_introl eq_refl))) as PD.
  set (common:=addM M bound (succM M count)).
  assert (HBoundTotal:source_bounded M total common).
  { exact (source_bounded_monotone M total bound common HTB (coding_le_add M bound (succM M count))). }
  assert (HBoundMono:source_bounded M mono common).
  { exact (source_bounded_monotone M mono bound common HMB (coding_le_add M bound (succM M count))). }
  pose proof (source_oc_output_bounded M phi (code_numeral M 1) output count HB
    ltac:(apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M count)));apply coding_zero_lt_succ) HO) as HOB.
  assert (HBoundOutput:source_bounded M output common).
  { apply (source_bounded_monotone M output (succM M count) common HOB).
    unfold common. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (HC:context_bounded M b c n common).
  { exact (context_bounded_monotone M b c n (zeroM M) common (proj1 HContext) (coding_zero_lt_succ M common)). }
  destruct (environment_cons_total M b c n total) as (tb&tc&tn&HConsT).
  destruct (environment_cons_total M tb tc tn mono) as (mb&mc&mn&HConsM).
  assert (HCT:context_bounded M tb tc tn common).
  { exact (proj2 (context_bounded_cons M b c n total tb tc tn common HConsT) (conj HBoundTotal HC)). }
  assert (HCM:context_bounded M mb mc mn common).
  { exact (proj2 (context_bounded_cons M tb tc tn mono mb mc mn common HConsM) (conj HBoundMono HCT)). }
  assert (Incl:context_included M b c n mb mc mn).
  { intros f HF. apply (source_cons_tail_inclusion M tb tc tn mono mb mc mn HConsM).
    exact (source_cons_tail_inclusion M b c n total tb tc tn HConsT f HF). }
  assert (PT:source_full_prv M mb mc mn total).
  { apply full_source_Ctx;[exists common;auto|].
    apply (source_cons_tail_inclusion M tb tc tn mono mb mc mn HConsM).
    apply (proj2 (context_member_cons M b c n total tb tc tn total HConsT)). now left. }
  assert (PM:source_full_prv M mb mc mn mono).
  { apply full_source_Ctx;[exists common;auto|].
    apply (proj2 (context_member_cons M tb tc tn mono mb mc mn mono HConsM)). now left. }
  pose proof (source_full_ordinal_collection_plan M mb mc mn phi total mono output envelope leastDouble count
    HB HO HPlan (source_full_prv_weaken_bounded M b c n mb mc mn envelope common PE Incl HCM) PT PM
    (source_full_prv_weaken_bounded M b c n mb mc mn leastDouble common PD Incl HCM)) as POutput.
  assert (HTailBound:source_bounded M tail common).
  { exact (proj2 (source_bounded_accept_binary M SFImpl mono output tail common
      (or_intror (or_intror eq_refl)) HTail) (conj HBoundMono HBoundOutput)). }
  assert (HImpBound:source_bounded M implication common).
  { exact (proj2 (source_bounded_accept_binary M SFImpl total tail implication common
      (or_intror (or_intror eq_refl)) HImp) (conj HBoundTotal HTailBound)). }
  pose proof (full_source_II M tb tc tn mono output tail mb mc mn
    (ex_intro _ common (conj HTailBound HCT)) POutput HConsM HTail) as PTail.
  exists b,c,n. split;[exact (proj1 (source_zfr_descriptor_context M b c n) HContext)|].
  exact (full_source_II M b c n total tail implication tb tc tn
    (ex_intro _ common (conj HImpBound HC)) PTail HConsT HImp).
Qed.

Print Assumptions source_zfr_ordinal_collection_theorem_bounded.

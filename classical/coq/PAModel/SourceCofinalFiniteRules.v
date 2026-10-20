(** Actual finite-theorem combination by source context weakening, II and
    IE. The cofinal induction below supplies all the inference callbacks. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceTraceBounds SourceBoundMonotone NumericalContexts NumericalSourceFull SourceProofWeakening
 SourceAxiomContexts SourceDescriptorProvability SourceFiniteProofContexts SourceSetTheoryDescriptors SourceZFRProvability SourceFiniteTelescope.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_finite_telescope_rule M known A target result k:
 (forall f,In f known ->source_zfr_provable M f) ->
 (forall f,In f A ->source_bounded M f k) ->source_bounded M target k ->
 source_finite_telescope M A target result ->
 (forall b c n,context_bounded M b c n k ->
  (forall f,In f known ->source_full_prv M b c n f) ->
  (forall f,In f A ->source_full_prv M b c n f) ->source_full_prv M b c n target) ->
 source_zfr_provable M result.
Proof.
 intros PK BA BT HT Rule.
 assert(HD:forall f,In f known ->source_descriptor_provable M ZFRSourceDescriptor f).
 { intros f HF. exact(proj2(source_zfr_descriptor_provable M f)(PK f HF)). }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor known HD)as(b&c&n&HBase&P).
 pose proof(proj1 HBase)as HClosed.
 pose proof(context_bounded_monotone M b c n(zeroM M)k HClosed(coding_zero_lt_succ M k))as HC.
 apply(proj1(source_zfr_descriptor_provable M result)). exists b,c,n. split;[exact HBase|].
 apply(source_full_finite_telescope M A target result k BA BT HT b c n HC).
 intros db dc dn HDC HIncl PA. apply(Rule db dc dn HDC);[|exact PA].
 intros f HF. exact(source_full_prv_weaken_bounded M b c n db dc dn f k(P f HF)HIncl HDC).
Qed.
Print Assumptions source_zfr_finite_telescope_rule.

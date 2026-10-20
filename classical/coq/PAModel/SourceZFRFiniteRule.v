(** Combine actual finite ZFR laws and curry an ordinary source derivation. *)
From PAModel Require Import Model FiniteCoding NumericalContexts NumericalSourceFull SourceBounded SourceBoundMonotone
 SourceTraceBounds SourceFiniteTelescope SourceFiniteProofContexts SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceProofWeakening.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_finite_rule M laws A target out k:
 (forall a,In a A ->source_bounded M a k) ->source_bounded M target k ->source_finite_telescope M A target out ->
 (forall law,In law laws ->source_zfr_provable M law) ->
 (forall b c n,context_bounded M b c n k ->(forall law,In law laws ->source_full_prv M b c n law) ->
  (forall a,In a A ->source_full_prv M b c n a) ->source_full_prv M b c n target) ->source_zfr_provable M out.
Proof.
 intros BA BT HO Laws Rule.
 assert(PL:forall law,In law laws ->source_descriptor_provable M ZFRSourceDescriptor law).
 { intros law HL. exact(proj2(source_zfr_descriptor_provable M law)(Laws law HL)). }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor laws PL)as(cb&cc&cn&HC&P).
 pose proof(source_zfr_context_closed M cb cc cn(proj1(source_zfr_descriptor_context M cb cc cn)HC))as BC.
 exists cb,cc,cn. split;[exact(proj1(source_zfr_descriptor_context M cb cc cn)HC)|].
 apply(source_full_finite_telescope M A target out k BA BT HO cb cc cn
  (context_bounded_monotone M cb cc cn(zeroM M)k BC(coding_zero_lt_succ M k))).
 intros b c n BContext Included Premises. apply(Rule b c n BContext);[|exact Premises].
 intros law HL. exact(source_full_prv_weaken_bounded M cb cc cn b c n law k(P law HL)Included BContext).
Qed.
Print Assumptions source_zfr_finite_rule.

(** Actual discharge of an externally finite telescope of ZFR proofs. *)
From PAModel Require Import Model SetFormulaCodes SourceFiniteTelescope
 SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_finite_telescope_apply M A target law:
 source_finite_telescope M A target law ->source_zfr_provable M law ->
 (forall a,In a A ->source_zfr_provable M a) ->source_zfr_provable M target.
Proof.
 revert law. induction A as[|a A IH];intros law HL PL PA.
 - change(law=target)in HL. now subst law.
 - destruct HL as(inner&HInner&HImpl).
   apply(IH inner HInner).
   + apply(proj1(source_zfr_descriptor_provable M inner)).
     exact(source_descriptor_provable_mp M ZFRSourceDescriptor a inner law
      (proj2(source_zfr_descriptor_provable M a)(PA a(or_introl eq_refl)))
      (proj2(source_zfr_descriptor_provable M law)PL)HImpl).
   + intros b HB. apply PA. now right.
Qed.
Print Assumptions source_zfr_finite_telescope_apply.

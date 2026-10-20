(** Actual universal elimination preserves arbitrary source descriptors. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes NumericalContexts
  NumericalInstantiation NumericalSourceFull SourceInstantiationConstructors
  SourceDescriptorProvability.
Unset Implicit Arguments.

Theorem source_descriptor_provable_all_elim M T a f t g :
  source_descriptor_provable M T f -> sf_relation M SFAll a (zeroM M) f ->
  numerical_instantiation M a t g -> source_descriptor_provable M T g.
Proof.
  intros (b&c&n&HC&HP) HF HG. exists b,c,n. split;[exact HC|].
  apply (full_source_AllE M b c n a f t g).
  - exact (source_wf_quantifier_instance M b c n SFAll a f t g (or_introl eq_refl)
      HF (source_full_prv_wellformed M b c n f HP) HG).
  - exact HP.
  - exact HF.
  - exact HG.
Qed.
Print Assumptions source_descriptor_provable_all_elim.

(** Actual instantiation and axiom introduction for source ZFC proofs. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes SourceBounded NumericalZFCAxioms ClosedSourceQuotation
  NumericalContexts NumericalEnvironments NumericalInstantiation SourceInstantiationConstructors
  SourceSequents NumericalSourceFull SourceZFCProvability.
Unset Implicit Arguments.

Theorem source_zfc_provable_axiom M f :
  numerical_zfc_source_axiom M f -> source_zfc_provable M f.
Proof.
  intro HF. destruct (context_singleton_total M f) as (b&c&n&HC).
  assert (HZ:source_zfc_context M b c n).
  { intros g HG. apply (proj1 (context_singleton_member M f b c n g HC)) in HG.
    now subst g. }
  exists b,c,n. split;[exact HZ|]. apply full_source_Ctx.
  - exists (zeroM M). split.
    + exact (numerical_zfc_source_axiom_closed M f HF).
    + exact (source_zfc_context_closed M b c n HZ).
  - apply (proj2 (context_singleton_member M f b c n f HC)). reflexivity.
Qed.

Theorem source_zfc_provable_all_elim M a f t g :
  source_zfc_provable M f -> sf_relation M SFAll a (zeroM M) f ->
  numerical_instantiation M a t g -> source_zfc_provable M g.
Proof.
  intros (b&c&n&HC&HP) HF HG. exists b,c,n. split;[exact HC|].
  apply (full_source_AllE M b c n a f t g).
  - exact (source_wf_quantifier_instance M b c n SFAll a f t g (or_introl eq_refl)
      HF (source_full_prv_wellformed M b c n f HP) HG).
  - exact HP.
  - exact HF.
  - exact HG.
Qed.

Print Assumptions source_zfc_provable_axiom.
Print Assumptions source_zfc_provable_all_elim.

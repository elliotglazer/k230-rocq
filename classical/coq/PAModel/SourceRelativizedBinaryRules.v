(** Binary FullND rules under the actual internal relativization map. *)
From PAModel Require Import Model SourceSequents SetFormulaCodes SetCodeDescent
  NumericalSourceFull SourceBounded SourceRelativization SourceRelativizationFunctionality
  SourceRelativizedContexts SourceRelativizedPropositional.
Unset Implicit Arguments.

Lemma source_relativized_binary_graph M dom h a d f ra rd rf :
  sf_binary h -> sf_relation M h a d f ->
  source_relativization M dom a ra -> source_relativization M dom d rd ->
  source_relativization M dom f rf -> sf_relation M h ra rd rf.
Proof.
  intros HB HF HA HD HR.
  destruct (sf_relation_total M h ra rd) as [g HG].
  pose proof (source_relativization_binary M dom h a d f ra rd g HB HF HA HD HG) as HRG.
  assert (g=rf) by exact (source_relativization_functional M f dom g rf HRG HR).
  now subst g.
Qed.

Section Rules.
Variable M : Model.
Variables dom b c n u v a d f ra rd rf : carrier M.
Hypothesis HDomain : source_bounded M dom (succM M (zeroM M)).
Hypothesis HContext : source_context_relativization M dom b c n u v.
Hypothesis HA : source_relativization M dom a ra.
Hypothesis HD : source_relativization M dom d rd.
Hypothesis HF : source_relativization M dom f rf.

Theorem source_relativized_CE1 :
  source_sequent_wf M b c n a -> sf_relation M SFAnd a d f ->
  source_full_prv M u v n rf -> source_full_prv M u v n ra.
Proof.
  intros HW HG HP. apply (full_source_CE1 M u v n ra rd rf).
  - exact (source_relativized_sequent_wf M dom b c n u v a ra HDomain HContext HA HW).
  - exact HP.
  - exact (source_relativized_binary_graph M dom SFAnd a d f ra rd rf
      (or_introl eq_refl) HG HA HD HF).
Qed.

Theorem source_relativized_CE2 :
  source_sequent_wf M b c n d -> sf_relation M SFAnd a d f ->
  source_full_prv M u v n rf -> source_full_prv M u v n rd.
Proof.
  intros HW HG HP. apply (full_source_CE2 M u v n ra rd rf).
  - exact (source_relativized_sequent_wf M dom b c n u v d rd HDomain HContext HD HW).
  - exact HP.
  - exact (source_relativized_binary_graph M dom SFAnd a d f ra rd rf
      (or_introl eq_refl) HG HA HD HF).
Qed.

Theorem source_relativized_CI :
  source_sequent_wf M b c n f -> sf_relation M SFAnd a d f ->
  source_full_prv M u v n ra -> source_full_prv M u v n rd -> source_full_prv M u v n rf.
Proof.
  intros HW HG PA PD. apply (full_source_CI M u v n ra rd rf).
  - exact (source_relativized_sequent_wf M dom b c n u v f rf HDomain HContext HF HW).
  - exact PA.
  - exact PD.
  - exact (source_relativized_binary_graph M dom SFAnd a d f ra rd rf
      (or_introl eq_refl) HG HA HD HF).
Qed.

Theorem source_relativized_IE :
  source_sequent_wf M b c n d -> sf_relation M SFImpl a d f ->
  source_full_prv M u v n rf -> source_full_prv M u v n ra -> source_full_prv M u v n rd.
Proof.
  intros HW HG PF PA. apply (full_source_IE M u v n ra rd rf).
  - exact (source_relativized_sequent_wf M dom b c n u v d rd HDomain HContext HD HW).
  - exact PF.
  - exact PA.
  - exact (source_relativized_binary_graph M dom SFImpl a d f ra rd rf
      (or_intror (or_intror eq_refl)) HG HA HD HF).
Qed.

Theorem source_relativized_DI1 :
  source_sequent_wf M b c n f -> sf_relation M SFOr a d f ->
  source_full_prv M u v n ra -> source_full_prv M u v n rf.
Proof.
  intros HW HG PA. apply (full_source_DI1 M u v n ra rd rf).
  - exact (source_relativized_sequent_wf M dom b c n u v f rf HDomain HContext HF HW).
  - exact PA.
  - exact (source_relativized_binary_graph M dom SFOr a d f ra rd rf
      (or_intror (or_introl eq_refl)) HG HA HD HF).
Qed.

Theorem source_relativized_DI2 :
  source_sequent_wf M b c n f -> sf_relation M SFOr a d f ->
  source_full_prv M u v n rd -> source_full_prv M u v n rf.
Proof.
  intros HW HG PD. apply (full_source_DI2 M u v n ra rd rf).
  - exact (source_relativized_sequent_wf M dom b c n u v f rf HDomain HContext HF HW).
  - exact PD.
  - exact (source_relativized_binary_graph M dom SFOr a d f ra rd rf
      (or_intror (or_introl eq_refl)) HG HA HD HF).
Qed.
End Rules.

Print Assumptions source_relativized_binary_graph.
Print Assumptions source_relativized_CE1.
Print Assumptions source_relativized_CE2.
Print Assumptions source_relativized_CI.
Print Assumptions source_relativized_IE.
Print Assumptions source_relativized_DI1.
Print Assumptions source_relativized_DI2.

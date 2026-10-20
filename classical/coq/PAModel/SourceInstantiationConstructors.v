(** Literal source instantiation constructors and the ordinary finite
    wellformedness side conditions needed by the source proof rules. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone SourceSequents SourceTraceBounds
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation.
Unset Implicit Arguments.

Theorem source_instantiation_binary M h a d f t x y v :
  sf_binary h -> sf_relation M h a d f ->
  numerical_instantiation M a t x -> numerical_instantiation M d t y ->
  sf_relation M h x y v -> numerical_instantiation M f t v.
Proof.
  intros HH HF [b [c [HB HX]]] [e [j [HE HY]]] HV.
  exists b,c. split;[exact HB|].
  apply (proj2 (numerical_substitution_binary M h a d f b c
    (succM M (zeroM M)) (zeroM M) v HH HF)).
  exists x,y. repeat split;try assumption.
  apply (proj1 (numerical_substitution_extensional M d e j
    (succM M (zeroM M)) b c (succM M (zeroM M)) (zeroM M) y
    (substitution_singletons_equivalent M e j b c t HE HB))). exact HY.
Qed.

Theorem source_wf_binary M b c n h a d f :
  sf_binary h -> sf_relation M h a d f ->
  source_sequent_wf M b c n a -> source_sequent_wf M b c n d ->
  source_sequent_wf M b c n f.
Proof.
  intros HH HF [ka [HA HC]] [kd [HD _]].
  exists (addM M ka kd). split.
  - apply (proj2 (source_bounded_accept_binary M h a d f (addM M ka kd) HH HF)). split.
    + exact (source_bounded_monotone M a ka (addM M ka kd) HA (coding_le_add M ka kd)).
    + apply (source_bounded_monotone M d kd (addM M ka kd) HD).
      rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact (context_bounded_monotone M b c n ka (addM M ka kd) HC (coding_le_add M ka kd)).
Qed.

Theorem source_wf_binary_left M b c n h a d f :
  sf_binary h -> sf_relation M h a d f -> source_sequent_wf M b c n f ->
  source_sequent_wf M b c n a.
Proof.
  intros HH HF [k [H HC]]. exists k. split;[|exact HC].
  exact (proj1 (proj1 (source_bounded_accept_binary M h a d f k HH HF) H)).
Qed.

Theorem source_wf_binary_right M b c n h a d f :
  sf_binary h -> sf_relation M h a d f -> source_sequent_wf M b c n f ->
  source_sequent_wf M b c n d.
Proof.
  intros HH HF [k [H HC]]. exists k. split;[|exact HC].
  exact (proj2 (proj1 (source_bounded_accept_binary M h a d f k HH HF) H)).
Qed.

Theorem source_wf_quantifier_instance M b c n h a f t g :
  (h=SFAll \/ h=SFEx) -> sf_relation M h a (zeroM M) f ->
  source_sequent_wf M b c n f -> numerical_instantiation M a t g ->
  source_sequent_wf M b c n g.
Proof.
  intros HH HF [k [HB HC]] HG.
  set (l:=succM M (addM M k t)).
  assert (HK:coding_lt M k (succM M l)).
  { apply (coding_lt_trans M k l (succM M l));[apply coding_le_add|apply coding_lt_succ]. }
  assert (HT:coding_lt M t l).
  { unfold l. rewrite Arithmetic.add_comm. apply coding_le_add. }
  exists l. split.
  - apply (numerical_instantiation_bounded M a t g l);[|exact HT|exact HG].
    apply (source_bounded_monotone M a (succM M k) (succM M l)).
    + exact (proj1 (source_bounded_accept_unary M h a f k HH HF) HB).
    + apply (proj2 (coding_lt_succ_cancel M k (succM M l))). exact HK.
  - exact (context_bounded_monotone M b c n k l HC HK).
Qed.

Print Assumptions source_instantiation_binary.
Print Assumptions source_wf_binary.
Print Assumptions source_wf_binary_left.
Print Assumptions source_wf_binary_right.
Print Assumptions source_wf_quantifier_instance.

(** Direct source-rule consumers of arithmetic relativization. These are
    proof constructions for internal formulas, not semantic truth claims. *)
From PAModel Require Import Model NumericalContexts SourceBounded SourceSequents
  NumericalSourceFull SetFormulaCodes SetCodeDescent SourceRelativization
  SourceRelativizationFunctionality SourceRelativizationBounds SourceRelativizedContexts.
Unset Implicit Arguments.

Theorem source_relativized_sequent_wf M dom b c n u v f g :
  source_bounded M dom (succM M (zeroM M)) ->
  source_context_relativization M dom b c n u v ->
  source_relativization M dom f g -> source_sequent_wf M b c n f ->
  source_sequent_wf M u v n g.
Proof.
  intros HD HC HR [k [HF HCtx]]. exists k;split.
  - exact (source_relativization_preserves_bound M f dom k g HD HF HR).
  - exact (source_context_relativization_preserves_bound M dom b c n u v k HD HC HCtx).
Qed.

Theorem source_relativized_Ctx M dom b c n u v f g :
  source_bounded M dom (succM M (zeroM M)) ->
  source_context_relativization M dom b c n u v -> source_relativization M dom f g ->
  source_sequent_wf M b c n f -> context_member M b c n f -> source_full_prv M u v n g.
Proof.
  intros HD HC HR HW HF. apply full_source_Ctx.
  - exact (source_relativized_sequent_wf M dom b c n u v f g HD HC HR HW).
  - apply (proj2 (source_context_relativization_member_iff M dom b c n u v g HC)).
    exists f;auto.
Qed.

Theorem source_relativized_Pc M dom b c n u v a d x y f g :
  source_bounded M dom (succM M (zeroM M)) ->
  source_context_relativization M dom b c n u v ->
  source_sequent_wf M b c n f -> source_relativization M dom f g ->
  sf_relation M SFImpl a d x -> sf_relation M SFImpl x a y -> sf_relation M SFImpl y a f ->
  source_full_prv M u v n g.
Proof.
  intros HD HC HW HR HX HY HF.
  assert (HB:sf_binary SFImpl) by (right;right;reflexivity).
  destruct (source_relativization_binary_inv M dom SFImpl y a f g HB HF HR)
    as [ry [ra [HRY [HRA HG]]]].
  destruct (source_relativization_binary_inv M dom SFImpl x a y ry HB HY HRY)
    as [rx [ra' [HRX [HRA' HGY]]]].
  assert (ra'=ra) by exact (source_relativization_functional M a dom ra' ra HRA' HRA).
  subst ra'.
  destruct (source_relativization_binary_inv M dom SFImpl a d x rx HB HX HRX)
    as [ra' [rd [HRA2 [HRD HGX]]]].
  assert (ra'=ra) by exact (source_relativization_functional M a dom ra' ra HRA2 HRA).
  subst ra'.
  exact (full_source_Pc M u v n ra rd rx ry g
    (source_relativized_sequent_wf M dom b c n u v f g HD HC HR HW) HGX HGY HG).
Qed.

Theorem source_relativized_Exp M dom b c n u v f g :
  source_bounded M dom (succM M (zeroM M)) ->
  source_context_relativization M dom b c n u v ->
  source_sequent_wf M b c n f -> source_relativization M dom f g ->
  source_full_prv M u v n (zeroM M) -> source_full_prv M u v n g.
Proof.
  intros HD HC HW HR HP. apply full_source_Exp;[|exact HP].
  exact (source_relativized_sequent_wf M dom b c n u v f g HD HC HR HW).
Qed.

Print Assumptions source_relativized_sequent_wf.
Print Assumptions source_relativized_Ctx.
Print Assumptions source_relativized_Pc.
Print Assumptions source_relativized_Exp.

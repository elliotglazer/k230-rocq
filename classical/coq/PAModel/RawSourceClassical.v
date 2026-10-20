(** Classical finite propositional certificates for canonical raw images.
    This is a proof construction in the existing numerical source calculus. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions CodeDescent NumericalProofs SetFormulaCodes SourceBounded SourceBoundMonotone
  NumericalContexts NumericalEnvironments SourceSequents SourceTraceBounds NumericalSourceFull
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawSourcePropositional.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem raw_source_context_extend_bounded M b c n bound a sa d e m :
  context_bounded M b c n bound -> raw_source_image M a sa ->
  environment_cons M b c n sa d e m -> exists k,context_bounded M d e m k.
Proof.
  intros HC HA HE. destruct (raw_source_image_bounded M a sa HA) as [l Hl].
  exists (addM M bound l).
  apply (proj2 (context_bounded_cons M b c n sa d e m _ HE)). split.
  - apply (source_bounded_monotone M sa l (addM M bound l) Hl).
    rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact (context_bounded_monotone M b c n bound (addM M bound l) HC (coding_le_add M bound l)).
Qed.

Theorem raw_source_peirce M cb cc cn bound a d x y f sf :
  context_bounded M cb cc cn bound ->
  implication_graph M a d x -> implication_graph M x a y -> implication_graph M y a f ->
  raw_source_image M f sf -> source_full_prv M cb cc cn sf.
Proof.
  intros HC HX HY HF HSF.
  destruct (raw_source_image_total M a) as [sa HA].
  destruct (raw_source_image_total M d) as [sd HD].
  destruct (raw_source_image_total M x) as [sx HSX].
  destruct (raw_source_image_total M y) as [sy HSY].
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) a) as [EA|[ap EA]].
  - subst a.
    destruct (environment_cons_total M cb cc cn sy) as (eb&ec&en&HE).
    apply (raw_source_implication_intro M cb cc cn bound y (zeroM M) f sy sa sf eb ec en
      HC HSY HA HSF HF HE).
    destruct (raw_source_context_extend_bounded M cb cc cn bound y sy eb ec en HC HSY HE) as [kb HCB].
    apply (source_full_truth M eb ec en sa).
    + exact (raw_source_image_sequent_wf M eb ec en kb (zeroM M) sa HCB HA).
    + exact (raw_source_zero_inv M sa HA).
  - assert (AN:a<>zeroM M).
    { change (a=succM M ap) in EA.
      intro E. apply (zero_ne_succ M ap). congruence. }
    assert (XN:x<>zeroM M).
    { intro E. subst x. exact (AN (proj1 (raw_zero_implication_arguments M a d HX))). }
    assert (YN:y<>zeroM M).
    { intro E. subst y. exact (AN (proj2 (raw_zero_implication_arguments M x a HY))). }
    assert (FN:f<>zeroM M).
    { intro E. subst f. exact (AN (proj2 (raw_zero_implication_arguments M y a HF))). }
    destruct (raw_source_implication_inv M a d x sx XN HX HSX) as (u&v&HU&HV&HXR).
    rewrite (raw_source_image_functional M a u sa HU HA),
      (raw_source_image_functional M d v sd HV HD) in HXR.
    destruct (raw_source_implication_inv M x a y sy YN HY HSY) as (u'&v'&HU'&HV'&HYR).
    rewrite (raw_source_image_functional M x u' sx HU' HSX),
      (raw_source_image_functional M a v' sa HV' HA) in HYR.
    destruct (raw_source_implication_inv M y a f sf FN HF HSF) as (u''&v''&HU''&HV''&HFR).
    rewrite (raw_source_image_functional M y u'' sy HU'' HSY),
      (raw_source_image_functional M a v'' sa HV'' HA) in HFR.
    exact (full_source_Pc M cb cc cn sa sd sx sy sf
      (raw_source_image_sequent_wf M cb cc cn bound f sf HC HSF) HXR HYR HFR).
Qed.

Print Assumptions raw_source_context_extend_bounded.
Print Assumptions raw_source_peirce.

(** Actual source proof rules for raw implication images. In particular,
    the raw zero collision is discharged by a source proof of truth. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  Pairing CodeExpressions CodeDescent CodeTags NumericalProofs SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  SourceSequents SourceTraceBounds NumericalSourceFull RawSourceImage
  RawSourceImageInversion RawSourceImageBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma raw_zero_implication M :
  implication_graph M (zeroM M) (zeroM M) (zeroM M).
Proof.
  apply implication_graph_tagged. exists (zeroM M). split;[apply pair_zero|].
  rewrite Arithmetic.mul_comm,Arithmetic.mul_zero,coding_add_zero. reflexivity.
Qed.

Theorem raw_zero_implication_arguments M a b :
  implication_graph M a b (zeroM M) -> a=zeroM M /\ b=zeroM M.
Proof.
  intro H. apply implication_graph_tagged in H.
  exact (proj2 (tagged_pair_decode_unique M 0 0 a b (zeroM M) (zeroM M)
    (zeroM M) ltac:(lia) ltac:(lia) H
    (proj1 (implication_graph_tagged M _ _ _) (raw_zero_implication M)))).
Qed.

Theorem raw_source_image_sequent_wf M b c n k f s :
  context_bounded M b c n k -> raw_source_image M f s ->
  source_sequent_wf M b c n s.
Proof.
  intros HC HS. destruct (raw_source_image_bounded M f s HS) as [l Hl].
  exists (addM M k l). split.
  - apply (source_bounded_monotone M s l (addM M k l) Hl).
    rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact (context_bounded_monotone M b c n k (addM M k l) HC (coding_le_add M k l)).
Qed.

Theorem source_full_truth M b c n s :
  source_sequent_wf M b c n s -> sf_relation M SFImpl (zeroM M) (zeroM M) s ->
  source_full_prv M b c n s.
Proof.
  intros HW HS. destruct HW as [k [HB HC]].
  destruct (environment_cons_total M b c n (zeroM M)) as (d&e&m&HE).
  apply (full_source_II M b c n (zeroM M) (zeroM M) s d e m).
  - exists k. auto.
  - apply full_source_Ctx.
    + exists k. split;[apply source_bounded_accept_falsity|].
      apply (proj2 (context_bounded_cons M b c n (zeroM M) d e m k HE)).
      split;[apply source_bounded_accept_falsity|exact HC].
    + apply (proj2 (context_member_cons M b c n (zeroM M) d e m (zeroM M) HE)). now left.
  - exact HE.
  - exact HS.
Qed.

Theorem raw_source_implication_intro M cb cc cn bound a b h sa sb sh d e m :
  context_bounded M cb cc cn bound ->
  raw_source_image M a sa -> raw_source_image M b sb -> raw_source_image M h sh ->
  implication_graph M a b h -> environment_cons M cb cc cn sa d e m ->
  source_full_prv M d e m sb -> source_full_prv M cb cc cn sh.
Proof.
  intros HC HA HB HH HImp HE HP.
  pose proof (raw_source_image_sequent_wf M cb cc cn bound h sh HC HH) as HW.
  destruct (environment_lt_cases M (zeroM M) h) as [Hpos|Hn].
  - assert (HN:h<>zeroM M).
    { intro E. subst h. exact (coding_not_lt_zero M _ Hpos). }
    destruct (raw_source_implication_inv M a b h sh HN HImp HH) as (u&v&HU&HV&HS).
    rewrite (raw_source_image_functional M a u sa HU HA) in HS.
    rewrite (raw_source_image_functional M b v sb HV HB) in HS.
    exact (full_source_II M cb cc cn sa sb sh d e m HW HP HE HS).
  - assert (E:h=zeroM M).
    { destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) h) as [E|[u E]];[exact E|].
      subst h. exfalso. exact (Hn (coding_zero_lt_succ M u)). }
    subst h. exact (source_full_truth M cb cc cn sh HW (raw_source_zero_inv M sh HH)).
Qed.

Theorem raw_source_implication_elim M cb cc cn bound a b h sa sb sh :
  context_bounded M cb cc cn bound ->
  raw_source_image M a sa -> raw_source_image M b sb -> raw_source_image M h sh ->
  implication_graph M a b h -> source_full_prv M cb cc cn sa ->
  source_full_prv M cb cc cn sh -> source_full_prv M cb cc cn sb.
Proof.
  intros HC HA HB HH HImp HP HQ.
  pose proof (raw_source_image_sequent_wf M cb cc cn bound b sb HC HB) as HW.
  destruct (environment_lt_cases M (zeroM M) h) as [Hpos|Hn].
  - assert (HN:h<>zeroM M).
    { intro E. subst h. exact (coding_not_lt_zero M _ Hpos). }
    destruct (raw_source_implication_inv M a b h sh HN HImp HH) as (u&v&HU&HV&HS).
    rewrite (raw_source_image_functional M a u sa HU HA) in HS.
    rewrite (raw_source_image_functional M b v sb HV HB) in HS.
    exact (full_source_IE M cb cc cn sa sb sh HW HQ HP HS).
  - assert (E:h=zeroM M).
    { destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) h) as [E|[u E]];[exact E|].
      subst h. exfalso. exact (Hn (coding_zero_lt_succ M u)). }
    subst h. destruct (raw_zero_implication_arguments M a b HImp) as [_ ->].
    exact (source_full_truth M cb cc cn sb HW (raw_source_zero_inv M sb HB)).
Qed.

Print Assumptions raw_zero_implication_arguments.
Print Assumptions raw_source_implication_intro.
Print Assumptions raw_source_implication_elim.

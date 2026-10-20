(** A fixed five-antecedent implication is constructed by literal source
    introduction. Its proof consumer is supplied by the proved macro. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceSequents SourceContextTransport SourceUpperProofHelpers SourceEmittedFrameRequest
  NumericalContexts NumericalEnvironments NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_five_premise_law M a1 a2 a3 a4 a5 target l5 l4 l3 l2 law k1 k2 k3 k4 k5 :
  source_bounded M a1 k1 ->source_bounded M a2 k2 ->source_bounded M a3 k3 ->
  source_bounded M a4 k4 ->source_bounded M a5 k5 ->
  sf_relation M SFImpl a5 target l5 ->sf_relation M SFImpl a4 l5 l4 ->
  sf_relation M SFImpl a3 l4 l3 ->sf_relation M SFImpl a2 l3 l2 ->sf_relation M SFImpl a1 l2 law ->
  (forall b c n,source_full_prv M b c n a1 ->source_full_prv M b c n a2 ->
    source_full_prv M b c n a3 ->source_full_prv M b c n a4 ->source_full_prv M b c n a5 ->
    source_full_prv M b c n target) ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) law.
Proof.
  intros B1 B2 B3 B4 B5 H5 H4 H3 H2 H1 Consume.
  assert (F0:source_context_finite_bound M (zeroM M)(zeroM M)(zeroM M)).
  { exists (zeroM M). apply context_bounded_empty. }
  destruct (environment_cons_total M (zeroM M)(zeroM M)(zeroM M) a1) as [b1 [c1 [n1 C1]]].
  destruct (source_full_assume M (zeroM M)(zeroM M)(zeroM M) a1 b1 c1 n1
    (source_wf_from_finite M (zeroM M)(zeroM M)(zeroM M) a1 k1 B1 F0) C1) as [F1 P1_1].
  destruct (environment_cons_total M b1 c1 n1 a2) as [b2 [c2 [n2 C2]]].
  destruct (source_full_assume M b1 c1 n1 a2 b2 c2 n2
    (source_wf_from_finite M b1 c1 n1 a2 k2 B2 F1) C2) as [F2 P2_2].
  pose proof (source_full_weaken_cons_finite M b1 c1 n1 a2 b2 c2 n2 a1
    C2 F2 P1_1) as P1_2.
  destruct (environment_cons_total M b2 c2 n2 a3) as [b3 [c3 [n3 C3]]].
  destruct (source_full_assume M b2 c2 n2 a3 b3 c3 n3
    (source_wf_from_finite M b2 c2 n2 a3 k3 B3 F2) C3) as [F3 P3_3].
  pose proof (source_full_weaken_cons_finite M b2 c2 n2 a3 b3 c3 n3 a1
    C3 F3 P1_2) as P1_3.
  pose proof (source_full_weaken_cons_finite M b2 c2 n2 a3 b3 c3 n3 a2
    C3 F3 P2_2) as P2_3.
  destruct (environment_cons_total M b3 c3 n3 a4) as [b4 [c4 [n4 C4]]].
  destruct (source_full_assume M b3 c3 n3 a4 b4 c4 n4
    (source_wf_from_finite M b3 c3 n3 a4 k4 B4 F3) C4) as [F4 P4_4].
  pose proof (source_full_weaken_cons_finite M b3 c3 n3 a4 b4 c4 n4 a1
    C4 F4 P1_3) as P1_4.
  pose proof (source_full_weaken_cons_finite M b3 c3 n3 a4 b4 c4 n4 a2
    C4 F4 P2_3) as P2_4.
  pose proof (source_full_weaken_cons_finite M b3 c3 n3 a4 b4 c4 n4 a3
    C4 F4 P3_3) as P3_4.
  destruct (environment_cons_total M b4 c4 n4 a5) as [b5 [c5 [n5 C5]]].
  destruct (source_full_assume M b4 c4 n4 a5 b5 c5 n5
    (source_wf_from_finite M b4 c4 n4 a5 k5 B5 F4) C5) as [F5 P5_5].
  pose proof (source_full_weaken_cons_finite M b4 c4 n4 a5 b5 c5 n5 a1
    C5 F5 P1_4) as P1_5.
  pose proof (source_full_weaken_cons_finite M b4 c4 n4 a5 b5 c5 n5 a2
    C5 F5 P2_4) as P2_5.
  pose proof (source_full_weaken_cons_finite M b4 c4 n4 a5 b5 c5 n5 a3
    C5 F5 P3_4) as P3_5.
  pose proof (source_full_weaken_cons_finite M b4 c4 n4 a5 b5 c5 n5 a4
    C5 F5 P4_4) as P4_5.
  pose proof (Consume b5 c5 n5 P1_5 P2_5 P3_5 P4_5 P5_5) as PT.
  pose proof (source_full_implication_intro M b4 c4 n4 a5 target l5
    b5 c5 n5 C5 H5 PT) as PL5.
  pose proof (source_full_implication_intro M b3 c3 n3 a4 l5 l4
    b4 c4 n4 C4 H4 PL5) as PL4.
  pose proof (source_full_implication_intro M b2 c2 n2 a3 l4 l3
    b3 c3 n3 C3 H3 PL4) as PL3.
  pose proof (source_full_implication_intro M b1 c1 n1 a2 l3 l2
    b2 c2 n2 C2 H2 PL3) as PL2.
  pose proof (source_full_implication_intro M (zeroM M)(zeroM M)(zeroM M) a1 l2 law
    b1 c1 n1 C1 H1 PL2) as PL1.
  exact PL1.
Qed.

Print Assumptions source_full_five_premise_law.

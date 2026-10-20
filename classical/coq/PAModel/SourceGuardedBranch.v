(** Replace the two explicit branch assumptions D and body by their
    conjunction using implication introduction, weakening and elimination. *)
From PAModel Require Import Model SetFormulaCodes SourceBounded NumericalContexts
  NumericalEnvironments SourceSequents NumericalSourceFull SourceProofWeakening.
Unset Implicit Arguments.

Theorem source_guarded_branch_from_two M b c n domain body f guard
    db dc dn ab ac an gb gc gn :
  environment_cons M b c n domain db dc dn ->
  environment_cons M db dc dn body ab ac an ->
  environment_cons M b c n guard gb gc gn ->
  sf_relation M SFAnd domain body guard ->
  source_full_prv M ab ac an f -> source_full_prv M gb gc gn f.
Proof.
  intros HD HA HG HGuard P.
  destruct (source_full_prv_wellformed M ab ac an f P) as [k [HF HABC]].
  destruct (proj1 (context_bounded_cons M db dc dn body ab ac an k HA) HABC) as [HBody HDBC].
  destruct (proj1 (context_bounded_cons M b c n domain db dc dn k HD) HDBC) as [HDomain HBC].
  assert (HGuardBound:source_bounded M guard k).
  { apply (proj2 (source_bounded_accept_binary M SFAnd domain body guard k (or_introl eq_refl) HGuard)). auto. }
  assert (HGBC:context_bounded M gb gc gn k).
  { apply (proj2 (context_bounded_cons M b c n guard gb gc gn k HG)). auto. }
  destruct (sf_relation_total M SFImpl body f) as [impA HImpA].
  destruct (sf_relation_total M SFImpl domain impA) as [impD HImpD].
  assert (HBA:source_bounded M impA k).
  { apply (proj2 (source_bounded_accept_binary M SFImpl body f impA k
      (or_intror (or_intror eq_refl)) HImpA)). auto. }
  assert (HBD:source_bounded M impD k).
  { apply (proj2 (source_bounded_accept_binary M SFImpl domain impA impD k
      (or_intror (or_intror eq_refl)) HImpD)). auto. }
  assert (PA:source_full_prv M db dc dn impA).
  { apply (full_source_II M db dc dn body f impA ab ac an);try assumption.
    exists k. auto. }
  assert (PD:source_full_prv M b c n impD).
  { apply (full_source_II M b c n domain impA impD db dc dn);try assumption.
    exists k. auto. }
  assert (PD':source_full_prv M gb gc gn impD).
  { apply (source_full_prv_weaken_bounded M b c n gb gc gn impD k PD);[|exact HGBC].
    intros a HMember. apply (proj2 (context_member_cons M b c n guard gb gc gn a HG)). now right. }
  assert (PG:source_full_prv M gb gc gn guard).
  { apply full_source_Ctx;[now exists k|].
    apply (proj2 (context_member_cons M b c n guard gb gc gn guard HG)). now left. }
  assert (PDomain:source_full_prv M gb gc gn domain).
  { apply (full_source_CE1 M gb gc gn domain body guard);try assumption. now exists k. }
  assert (PBody:source_full_prv M gb gc gn body).
  { apply (full_source_CE2 M gb gc gn domain body guard);try assumption. now exists k. }
  assert (PA':source_full_prv M gb gc gn impA).
  { apply (full_source_IE M gb gc gn domain impA impD);try assumption. now exists k. }
  apply (full_source_IE M gb gc gn body f impA);try assumption. now exists k.
Qed.

Print Assumptions source_guarded_branch_from_two.

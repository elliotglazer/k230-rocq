(** The actual ZFR monotonicity theorem, with both fixed hierarchy laws
    constructed internally and all four ordinary assumptions discharged. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull NumericalInstantiation
  SourceOrdinalPredicate SourceDomainInstances SourceRawSubset SourceRawSubsetBounds SourceD0At
  SourceD0Monotonicity SourceHierarchyExistsShell SourceHierarchySubsetShell SourceZFRProvability
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceFiniteProofContexts SourceLeastOrdinalWitness.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_zfr_d0_monotonicity M domain phi d e od oe subset d0d d0e t3 t2 t1 law k :
  source_bounded M domain (code_numeral M 1) ->source_bounded M phi (succM M k) ->
  coding_lt M d k ->coding_lt M e k ->
  numerical_instantiation M (source_ordinal_predicate_code M) d od ->
  numerical_instantiation M (source_ordinal_predicate_code M) e oe ->source_raw_subset_graph M d e subset ->
  source_d0_at M domain phi d d0d ->source_d0_at M domain phi e d0e ->
  sf_relation M SFImpl d0d d0e t3 ->sf_relation M SFImpl subset t3 t2 ->
  sf_relation M SFImpl oe t2 t1 ->sf_relation M SFImpl od t1 law ->source_zfr_provable M law.
Proof.
  intros HD HB HDN HEN HOD HOE HS HD0 HE0 HT3 HT2 HT1 HLaw.
  destruct (source_zfr_hierarchy_exists_shell M (succM M d)) as (ods&body&ex&lawEx&HEx&PEx).
  destruct (source_zfr_hierarchy_subset_shell M (succM M (succM M d)) (succM M (succM M e))
    (zeroM M) (code_numeral M 1)) as (odd&oee&sub2&ld2&le2&res&lawSub&HSub&PSub).
  assert (HLaws:source_d0_monotone_laws M d e lawEx lawSub).
  { split;[exists ods,body,ex;exact HEx|exists odd,oee,sub2,ld2,le2,res;exact HSub]. }
  assert (HP:forall f,In f [lawEx;lawSub] ->source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f [<-|[<-|[]]];apply (proj2 (source_zfr_descriptor_provable M _));assumption. }
  destruct (source_descriptor_finite_common_context M ZFRSourceDescriptor [lawEx;lawSub] HP)
    as (b&c&n&HContext&P).
  pose proof (P lawEx (or_introl eq_refl)) as PExLaw.
  pose proof (P lawSub (or_intror (or_introl eq_refl))) as PSubLaw.
  pose proof (source_domain_instance_bound M (source_ordinal_predicate_code M) d od k
    (source_ordinal_predicate_bounded M) HDN HOD) as BOD.
  pose proof (source_domain_instance_bound M (source_ordinal_predicate_code M) e oe k
    (source_ordinal_predicate_bounded M) HEN HOE) as BOE.
  pose proof (source_raw_subset_bounded M d e subset k HDN HEN HS) as BS.
  pose proof (source_d0_at_bounded M domain phi d d0d k HD HB HDN HD0) as BD.
  pose proof (source_d0_at_bounded M domain phi e d0e k HD HB HEN HE0) as BE.
  assert (BT3:source_bounded M t3 k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl d0d d0e t3 k
      (or_intror (or_intror eq_refl)) HT3) (conj BD BE)). }
  assert (BT2:source_bounded M t2 k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl subset t3 t2 k
      (or_intror (or_intror eq_refl)) HT2) (conj BS BT3)). }
  assert (BT1:source_bounded M t1 k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl oe t2 t1 k
      (or_intror (or_intror eq_refl)) HT1) (conj BOE BT2)). }
  assert (BLaw:source_bounded M law k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl od t1 law k
      (or_intror (or_intror eq_refl)) HLaw) (conj BOD BT1)). }
  pose proof (context_bounded_monotone M b c n (zeroM M) k (proj1 HContext) (coding_zero_lt_succ M k)) as HC.
  destruct (environment_cons_total M b c n od) as (b1&c1&n1&H1).
  pose proof (proj2 (context_bounded_cons M b c n od b1 c1 n1 k H1) (conj BOD HC)) as HC1.
  destruct (environment_cons_total M b1 c1 n1 oe) as (b2&c2&n2&H2).
  pose proof (proj2 (context_bounded_cons M b1 c1 n1 oe b2 c2 n2 k H2) (conj BOE HC1)) as HC2.
  destruct (environment_cons_total M b2 c2 n2 subset) as (b3&c3&n3&H3).
  pose proof (proj2 (context_bounded_cons M b2 c2 n2 subset b3 c3 n3 k H3) (conj BS HC2)) as HC3.
  destruct (environment_cons_total M b3 c3 n3 d0d) as (b4&c4&n4&H4).
  pose proof (proj2 (context_bounded_cons M b3 c3 n3 d0d b4 c4 n4 k H4) (conj BD HC3)) as HC4.
  assert (Incl:context_included M b c n b4 c4 n4).
  { intros f HF. apply (source_cons_tail_inclusion M b3 c3 n3 d0d b4 c4 n4 H4).
    apply (source_cons_tail_inclusion M b2 c2 n2 subset b3 c3 n3 H3).
    apply (source_cons_tail_inclusion M b1 c1 n1 oe b2 c2 n2 H2).
    exact (source_cons_tail_inclusion M b c n od b1 c1 n1 H1 f HF). }
  assert (POD:source_full_prv M b4 c4 n4 od).
  { apply full_source_Ctx;[exists k;auto|].
    apply (source_cons_tail_inclusion M b3 c3 n3 d0d b4 c4 n4 H4).
    apply (source_cons_tail_inclusion M b2 c2 n2 subset b3 c3 n3 H3).
    apply (source_cons_tail_inclusion M b1 c1 n1 oe b2 c2 n2 H2).
    apply (proj2 (context_member_cons M b c n od b1 c1 n1 od H1)). now left. }
  assert (POE:source_full_prv M b4 c4 n4 oe).
  { apply full_source_Ctx;[exists k;auto|].
    apply (source_cons_tail_inclusion M b3 c3 n3 d0d b4 c4 n4 H4).
    apply (source_cons_tail_inclusion M b2 c2 n2 subset b3 c3 n3 H3).
    apply (proj2 (context_member_cons M b1 c1 n1 oe b2 c2 n2 oe H2)). now left. }
  assert (PS:source_full_prv M b4 c4 n4 subset).
  { apply full_source_Ctx;[exists k;auto|].
    apply (source_cons_tail_inclusion M b3 c3 n3 d0d b4 c4 n4 H4).
    apply (proj2 (context_member_cons M b2 c2 n2 subset b3 c3 n3 subset H3)). now left. }
  assert (PD:source_full_prv M b4 c4 n4 d0d).
  { apply full_source_Ctx;[exists k;auto|].
    apply (proj2 (context_member_cons M b3 c3 n3 d0d b4 c4 n4 d0d H4)). now left. }
  pose proof (source_full_d0_monotone M b4 c4 n4 b c n k domain phi d e od oe subset d0d d0e lawEx lawSub
    HC4 (proj1 HContext) Incl HD HB HDN HEN HOD HOE HS HD0 HE0 HLaws PExLaw PSubLaw POD POE PS PD) as PGoal.
  pose proof (full_source_II M b3 c3 n3 d0d d0e t3 b4 c4 n4
    (ex_intro _ k (conj BT3 HC3)) PGoal H4 HT3) as P3.
  pose proof (full_source_II M b2 c2 n2 subset t3 t2 b3 c3 n3
    (ex_intro _ k (conj BT2 HC2)) P3 H3 HT2) as P2.
  pose proof (full_source_II M b1 c1 n1 oe t2 t1 b2 c2 n2
    (ex_intro _ k (conj BT1 HC1)) P2 H2 HT1) as P1.
  exists b,c,n. split;[exact (proj1 (source_zfr_descriptor_context M b c n) HContext)|].
  exact (full_source_II M b c n od t1 law b1 c1 n1 (ex_intro _ k (conj BLaw HC)) P1 H1 HLaw).
Qed.

Print Assumptions source_zfr_d0_monotonicity.

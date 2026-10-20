(** All named-universal commutation rows have actual source proofs.  Equal
    names give identity; distinct names use the checked internal double-map
    swap and native source generalization/specialization. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions CodeDescent
  NumericalProofs ProofTemplates SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone
  NumericalRenaming NumericalContexts RawBinderRenaming RawDoubleBinderSwap SourceSwap
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawEqualityCalibration
  RawFinitePropositional RawLogicalRow2 SourceUniversalCommutation SourceZFCProvability SourceZFCBasicClosure.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma raw_universal_functional M x body f g :
  universal_graph M x body f ->universal_graph M x body g ->f=g.
Proof.
  exact (code_relation_functional M (E_wal (CEvar 0) (CEvar 1))
    (arguments2 x body (zeroM M)) f g).
Qed.

Theorem raw_commutation_graph_source M a b body qa qb qab qba raw out :
  universal_graph M a body qa ->universal_graph M b body qb ->
  universal_graph M a qb qab ->universal_graph M b qa qba ->
  implication_graph M qab qba raw ->raw_source_image M raw out ->source_zfc_provable M out.
Proof.
  intros HQA HQB HQAB HQBA HR HO.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) a b) as [E|HNE].
  - subst b. assert (EQ:qb=qa) by exact (raw_universal_functional M a body qb qa HQB HQA).
    subst qb. assert (EQ:qba=qab) by exact (raw_universal_functional M a qa qba qab HQBA HQAB).
    subst qba. apply source_zfc_provable_from_empty.
    apply (raw_prop_certificate_empty_source M raw out);[|exact HO].
    apply (rpc_intro M [] qab qab raw HR). apply rpc_hyp. cbn;auto.
  - pose proof (raw_implication_nonzero_consequent M qab qba raw
      (raw_universal_nonzero M b qa qba HQBA) HR) as HRN.
    destruct (raw_source_implication_inv M qab qba raw out HRN HR HO)
      as (sqab&sqba&HQABI&HQBAI&HSOut).
    destruct (raw_source_universal_inv M a qb qab sqab HQAB HQABI)
      as (sqb&ab&ac&leftInner&HQBI&HMA&HRQB&HSLeftOuter).
    destruct (raw_source_universal_inv M b qa qba sqba HQBA HQBAI)
      as (sqa&bb&bc&rightInner&HQAI&HMB&HRQA&HSRightOuter).
    destruct (raw_source_universal_inv M b body qb sqb HQB HQBI)
      as (sf&bi&ci&fb&HBI&HMBI&HFB&HSQB).
    destruct (raw_source_universal_inv M a body qa sqa HQA HQAI)
      as (sf'&ai&aj&fa&HBI'&HMAI&HFA&HSQA).
    rewrite (raw_source_image_functional M body sf' sf HBI' HBI) in HFA.
    apply (proj1 (numerical_renaming_quantifier M true fb sqb ab ac
      (succM M a) (succM M (zeroM M)) leftInner HSQB)) in HRQB.
    destruct HRQB as (la&lc&ln&fab&HLA&HFAB&HSLeftInner).
    apply (proj1 (numerical_renaming_quantifier M true fa sqa bb bc
      (succM M b) (succM M (zeroM M)) rightInner HSQA)) in HRQA.
    destruct HRQA as (lb&ld&lm&fba&HLB&HFBA&HSRightInner).
    assert (HFA':numerical_renaming M sf ab ac (succM M a) (succM M (zeroM M)) fa).
    { apply (proj1 (numerical_renaming_extensional M sf ai aj (succM M a) ab ac
        (succM M a) (succM M (zeroM M)) fa
        (raw_binder_renaming_equivalent M a ai aj ab ac HMAI HMA))). exact HFA. }
    assert (HFB':numerical_renaming M sf bb bc (succM M b) (succM M (zeroM M)) fb).
    { apply (proj1 (numerical_renaming_extensional M sf bi ci (succM M b) bb bc
        (succM M b) (succM M (zeroM M)) fb
        (raw_binder_renaming_equivalent M b bi ci bb bc HMBI HMB))). exact HFB. }
    destruct (raw_source_image_bounded M body sf HBI) as (k&HFBound).
    destruct (source_swap_map_total M) as (p&q&HSwap).
    pose proof (raw_double_binder_swap M a b sf k fa fb fab fba
      ab ac bb bc la lc ln lb ld lm p q HNE HFBound HMA HMB HLA HLB
      HFA' HFB' HFAB HFBA HSwap) as HRSwap.
    destruct (raw_source_image_bounded M qab sqab HQABI) as (kl&HKL).
    destruct (raw_source_image_bounded M qba sqba HQBAI) as (kr&HKR).
    apply (proj1 (source_bounded_accept_unary M SFAll leftInner sqab kl
      (or_introl eq_refl) HSLeftOuter)) in HKL.
    apply (proj1 (source_bounded_accept_unary M SFAll fab leftInner (succM M kl)
      (or_introl eq_refl) HSLeftInner)) in HKL.
    apply (proj1 (source_bounded_accept_unary M SFAll rightInner sqba kr
      (or_introl eq_refl) HSRightOuter)) in HKR.
    apply (proj1 (source_bounded_accept_unary M SFAll fba rightInner (succM M kr)
      (or_introl eq_refl) HSRightInner)) in HKR.
    set (bound:=addM M (succM M (succM M kl)) (succM M (succM M kr))).
    assert (HBL:source_bounded M fab bound).
    { apply (source_bounded_monotone M fab (succM M (succM M kl)) bound HKL).
      apply coding_le_add. }
    assert (HBR:source_bounded M fba bound).
    { apply (source_bounded_monotone M fba (succM M (succM M kr)) bound HKR).
      unfold bound. rewrite Arithmetic.add_comm. apply coding_le_add. }
    apply source_zfc_provable_from_empty.
    exact (source_universal_commutation M fab fba leftInner sqab rightInner sqba out bound p q
      HBL HBR HSwap HRSwap HSLeftInner HSLeftOuter HSRightInner HSRightOuter HSOut).
Qed.

Theorem source_zfc_raw_row4 M env raw out :
  code_relation M env code_row4 raw ->raw_source_image M raw out ->source_zfc_provable M out.
Proof.
  intros HR HO.
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 2)) env) as (qa&HQA).
  destruct (code_relation_total M (E_wal (CEvar 1) (CEvar 2)) env) as (qb&HQB).
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wal (CEvar 1) (CEvar 2))) env) as (qab&HQAB).
  destruct (code_relation_total M (E_wal (CEvar 1) (E_wal (CEvar 0) (CEvar 2))) env) as (qba&HQBA).
  apply (raw_commutation_graph_source M (env 0) (env 1) (env 2) qa qb qab qba raw out).
  - exact (expression_universal_graph M env (CEvar 0) (CEvar 2) _ _ qa eq_refl eq_refl HQA).
  - exact (expression_universal_graph M env (CEvar 1) (CEvar 2) _ _ qb eq_refl eq_refl HQB).
  - exact (expression_universal_graph M env (CEvar 0) (E_wal (CEvar 1) (CEvar 2)) _ qb qab eq_refl HQB HQAB).
  - exact (expression_universal_graph M env (CEvar 1) (E_wal (CEvar 0) (CEvar 2)) _ qa qba eq_refl HQA HQBA).
  - exact (expression_implication_graph M env (E_wal (CEvar 0) (E_wal (CEvar 1) (CEvar 2)))
      (E_wal (CEvar 1) (E_wal (CEvar 0) (CEvar 2))) qab qba raw HQAB HQBA HR).
  - exact HO.
Qed.

Print Assumptions raw_commutation_graph_source.
Print Assumptions source_zfc_raw_row4.

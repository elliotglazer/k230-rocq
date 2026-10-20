From PAModel Require Import Model CodeExpressions NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenamingMaps NumericalRenaming NumericalTraces SourceBounded
  SourcePropositionalRules SourceQuantifierRules SourceSequents NumericalSourceFull SetFormulaCodes
  SourceRenamingInstances SourceProofRenamingInvariant SourceProofRenamingUnary SourceProofRenamingBinary.
Unset Implicit Arguments.

Theorem source_proof_renaming_full_unary M r p :
  source_proof_renaming_invariant M p -> source_full_unary M r p -> source_proof_renaming_invariant M r.
Proof.
  intros HP HRule. assert (HO:source_full_row M r).
  { apply (trace_derives_unary M source_full_rules r p (proj1 HP)). apply source_full_trace_unary. exact HRule. }
  destruct HRule as [H|[_ [H|[H|H]]]].
  - exact (source_proof_renaming_prop_unary M r p HP H).
  - destruct H as (b & c & n & a & f & sb & sc & HR & HS & HShift & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (renaming_lift_total M rb rc rn delta) as [rd [re [rm HL]]].
    destruct (numerical_renaming_total M a rd re rm delta) as [ar HA].
    destruct (context_shift_total M ub uc n) as [us [vs HT]].
    destruct (source_sequent_wf_from_row M b c n f r HR (source_full_row_wellformed M r HO)) as [k [_ HBound]].
    apply (full_source_AllI M ub uc n ar fr us vs).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + apply (proj1 (proj2 HP) sb sc n a rd re rm delta us vs ar HS);[|exact HA].
      exact (source_context_shift_renaming M b c n sb sc rb rc rn delta ub uc us vs rd re rm k HBound HShift HC HT HL).
    + exact HT.
    + exact (source_quantifier_renaming_graph M true a f rb rc rn delta rd re rm ar fr HF HL HA HFR).
  - destruct H as (b & c & n & a & f & t & g & HR & HS & HF & HG).
    apply (source_proof_renaming_ordinary_intro M r b c n g HO HR).
    intros rb rc rn delta ub uc gr HC HGR.
    destruct (renaming_lift_total M rb rc rn delta) as [rd [re [rm HL]]].
    destruct (numerical_renaming_total M a rd re rm delta) as [ar HA].
    destruct (numerical_renaming_total M f rb rc rn delta) as [fr HFR].
    destruct (renaming_lookup_total M rb rc rn delta t) as [tr HTR].
    destruct (source_sequent_wf_from_row M b c n f p HS (source_full_row_wellformed M p (proj1 HP))) as [k [HBound _]].
    assert (HAB:source_bounded M a (succM M k)).
    { exact (proj1 (source_bounded_accept_unary M SFAll a f k (or_introl eq_refl) HF) HBound). }
    apply (full_source_AllE M ub uc n ar fr tr gr).
    + exact (source_proof_renaming_target_wf M r b c n g rb rc rn delta ub uc gr HO HR HC HGR).
    + exact (proj1 (proj2 HP) b c n f rb rc rn delta ub uc fr HS HC HFR).
    + exact (source_quantifier_renaming_graph M true a f rb rc rn delta rd re rm ar fr HF HL HA HFR).
    + exact (source_instantiation_renaming M a t g rb rc rn delta rd re rm ar tr gr (succM M k) HAB HG HL HA HTR HGR).
  - destruct H as (b & c & n & a & f & t & g & HR & HS & HF & HG).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (renaming_lift_total M rb rc rn delta) as [rd [re [rm HL]]].
    destruct (numerical_renaming_total M a rd re rm delta) as [ar HA].
    destruct (numerical_renaming_total M g rb rc rn delta) as [gr HGR].
    destruct (renaming_lookup_total M rb rc rn delta t) as [tr HTR].
    destruct (source_sequent_wf_from_row M b c n f r HR (source_full_row_wellformed M r HO)) as [k [HBound _]].
    assert (HAB:source_bounded M a (succM M k)).
    { exact (proj1 (source_bounded_accept_unary M SFEx a f k (or_intror eq_refl) HF) HBound). }
    apply (full_source_ExI M ub uc n ar fr tr gr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (proj1 (proj2 HP) b c n g rb rc rn delta ub uc gr HS HC HGR).
    + exact (source_quantifier_renaming_graph M false a f rb rc rn delta rd re rm ar fr HF HL HA HFR).
    + exact (source_instantiation_renaming M a t g rb rc rn delta rd re rm ar tr gr (succM M k) HAB HG HL HA HTR HGR).
Qed.

Theorem source_proof_renaming_full_binary M r p q :
  source_proof_renaming_invariant M p -> source_proof_renaming_invariant M q ->
  source_full_binary M r p q -> source_proof_renaming_invariant M r.
Proof.
  intros HP HQ HRule. assert (HO:source_full_row M r).
  { apply (trace_derives_binary M source_full_rules r p q (proj1 HP) (proj1 HQ)).
    apply source_full_trace_binary. exact HRule. }
  destruct HRule as [H|[_ H]].
  - exact (source_proof_renaming_prop_binary M r p q HP HQ H).
  - destruct H as (b & c & n & a & ex & f & g & sb & sc & tb & tc & tn & HR & HS & HBranch & HEx & HShift & HCons & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (renaming_lift_total M rb rc rn delta) as [rd [re [rm HL]]].
    destruct (numerical_renaming_total M a rd re rm delta) as [ar HA].
    destruct (numerical_renaming_total M ex rb rc rn delta) as [exr HExR].
    destruct (numerical_renaming_total M g rd re rm delta) as [gr HGR].
    destruct (context_shift_total M ub uc n) as [us [vs HT]].
    destruct (environment_cons_total M us vs n ar) as [vb [vc [vn HNew]]].
    assert (EN:vn=tn) by (rewrite (proj1 HNew);symmetry;exact (proj1 HCons)). subst vn.
    destruct (source_sequent_wf_from_row M b c n f r HR (source_full_row_wellformed M r HO)) as [k [HB HBound]].
    assert (HShiftContext:context_renaming M sb sc n rd re rm delta us vs).
    { exact (source_context_shift_renaming M b c n sb sc rb rc rn delta ub uc us vs rd re rm k HBound HShift HC HT HL). }
    apply (full_source_ExE M ub uc n ar exr fr gr us vs vb vc tn).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (proj1 (proj2 HP) b c n ex rb rc rn delta ub uc exr HS HC HExR).
    + apply (proj1 (proj2 HQ) tb tc tn g rd re rm delta vb vc gr HBranch);[|exact HGR].
      exact (context_renaming_cons M sb sc n rd re rm delta us vs a ar tb tc tn vb vc HShiftContext HA HCons HNew).
    + exact (source_quantifier_renaming_graph M false a ex rb rc rn delta rd re rm ar exr HEx HL HA HExR).
    + exact HT.
    + exact HNew.
    + exact (source_shift_renaming M f g rb rc rn delta rd re rm fr gr k HB HF HL HFR HGR).
Qed.

Print Assumptions source_proof_renaming_full_unary.
Print Assumptions source_proof_renaming_full_binary.

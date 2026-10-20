(** Exact syntax of Z_ord.oc_form and its two source axiom instances.
    Ordinal is the one-free-variable Ord0 predicate, supplied as a code.
    This constructs required ZFR axioms, not a proof of ordinal collection. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded NumericalInstantiation SourceRelativizationBounds SourceFiniteCutoffShift SourceFixedSwap
  NumericalRenaming NumericalSubstitutionMaps SourceSchemaInstanceFormulas NumericalZFCAxioms NumericalTheories SourceSetTheoryDescriptors.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_oc_tail M phi out := exists shifted atom neg implication,
  source_cutoff_shift M 2 phi shifted /\ sf_relation M SFMember (zeroM M) (code_numeral M 2) atom /\
  sf_relation M SFImpl shifted (zeroM M) neg /\ sf_relation M SFImpl atom neg implication /\
  sf_relation M SFAll implication (zeroM M) out.
Definition source_oc_tail_formula (phi out:term) : form :=
  ∃∃∃∃ (source_cutoff_shift_formula 2 (lift4 phi) $3 ∧
    (sf_formula SFMember zero (num 2) $2 ∧ (sf_formula SFImpl $3 zero $1 ∧
    (sf_formula SFImpl $2 $1 $0 ∧ sf_formula SFAll $0 zero (lift4 out))))).
Definition source_oc_form M ordinal phi out := exists ord1 swapped tail inner,
  numerical_instantiation M ordinal (code_numeral M 1) ord1 /\
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) swapped /\
  source_oc_tail M phi tail /\ sf_relation M SFAnd ord1 swapped inner /\ sf_relation M SFAnd inner tail out.
Definition source_oc_form_formula (ordinal phi out:term) : form :=
  ∃∃∃∃ (numerical_instantiation_formula (lift4 ordinal) (num 1) $3 ∧
    (numerical_renaming_formula (lift4 phi) (num 3) (num 1) (num 2) zero $2 ∧
    (source_oc_tail_formula (lift4 phi) $1 ∧
    (sf_formula SFAnd $3 $2 $0 ∧ sf_formula SFAnd $0 $1 (lift4 out))))).
Local Opaque holds source_cutoff_shift_formula sf_formula numerical_instantiation_formula numerical_renaming_formula.

Theorem source_oc_tail_formula_correct M rho phi out :
  holds M rho (source_oc_tail_formula phi out) <-> source_oc_tail M (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_oc_tail_formula,source_oc_tail. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_cutoff_shift_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,lift4. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Local Opaque source_oc_tail_formula.
Theorem source_oc_form_formula_correct M rho ordinal phi out :
  holds M rho (source_oc_form_formula ordinal phi out) <->
  source_oc_form M (evalM M rho ordinal) (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_oc_form_formula,source_oc_form. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_oc_tail_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,lift4. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_oc_tail_total M phi : exists out,source_oc_tail M phi out.
Proof.
  destruct (source_cutoff_shift_total M 2 phi) as [shifted HS].
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 2)) as [atom HA].
  destruct (sf_relation_total M SFImpl shifted (zeroM M)) as [neg HN].
  destruct (sf_relation_total M SFImpl atom neg) as [implication HI].
  destruct (sf_relation_total M SFAll implication (zeroM M)) as [out HO].
  exists out,shifted,atom,neg,implication. exact (conj HS (conj HA (conj HN (conj HI HO)))).
Qed.
Theorem source_oc_form_total M ordinal phi : exists out,source_oc_form M ordinal phi out.
Proof.
  destruct (numerical_instantiation_total M ordinal (code_numeral M 1)) as [ord1 HOrd].
  destruct (numerical_renaming_total M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M)) as [swapped HS].
  destruct (source_oc_tail_total M phi) as [tail HT].
  destruct (sf_relation_total M SFAnd ord1 swapped) as [inner HI].
  destruct (sf_relation_total M SFAnd inner tail) as [out HO].
  exists out,ord1,swapped,tail,inner. exact (conj HOrd (conj HS (conj HT (conj HI HO)))).
Qed.

Theorem source_oc_tail_bounded M phi out n :
  source_bounded M phi (succM M (succM M n)) -> source_oc_tail M phi out ->
  source_bounded M out (succM M (succM M n)).
Proof.
  intros HP (shifted & atom & neg & implication & HS & HA & HN & HI & HO).
  apply (proj2 (source_bounded_accept_unary M SFAll implication out (succM M (succM M n)) (or_introl eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFImpl atom neg implication (succM M (succM M (succM M n)))
    (or_intror (or_intror eq_refl)) HI)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 2) atom
      (succM M (succM M (succM M n))) (or_introl eq_refl) HA)). split.
    + apply coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
  - apply (proj2 (source_bounded_accept_binary M SFImpl shifted (zeroM M) neg (succM M (succM M (succM M n)))
      (or_intror (or_intror eq_refl)) HN)). split.
    + exact (source_cutoff_shift_bounded M 2 phi shifted n HP HS).
    + apply source_bounded_accept_falsity.
Qed.
Theorem source_oc_form_bounded M ordinal phi out n :
  source_bounded M ordinal (code_numeral M 1) -> source_bounded M phi (succM M (succM M n)) ->
  source_oc_form M ordinal phi out -> source_bounded M out (succM M (succM M n)).
Proof.
  intros HD HP (ord1 & swapped & tail & inner & HOrd & HS & HT & HI & HO).
  apply (proj2 (source_bounded_accept_binary M SFAnd inner tail out (succM M (succM M n)) (or_introl eq_refl) HO)). split.
  - apply (proj2 (source_bounded_accept_binary M SFAnd ord1 swapped inner (succM M (succM M n)) (or_introl eq_refl) HI)). split.
    + exact (numerical_instantiation_bounded M ordinal (code_numeral M 1) ord1 (succM M (succM M n))
        (sr_domain_bound_succ M ordinal (succM M (succM M n)) HD)
        (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M n)) (coding_zero_lt_succ M n)) HOrd).
    + exact (source_fixed_swap_bounded M phi swapped n HP HS).
  - exact (source_oc_tail_bounded M phi tail n HP HT).
Qed.

Definition source_ordinal_collection_instances M ordinal phi n sep rep := exists oc,
  source_oc_form M ordinal phi oc /\ numerical_separation_instance M phi (succM M n) sep /\
  numerical_replacement_instance M oc n rep.
Definition source_ordinal_collection_instances_formula (ordinal phi n sep rep:term) : form :=
  ∃ (source_oc_form_formula ordinal`[↑] phi`[↑] $0 ∧
    (source_separation_instance_formula phi`[↑] (σ n`[↑]) sep`[↑] ∧
     source_replacement_instance_formula $0 n`[↑] rep`[↑])).
Local Opaque source_oc_form_formula source_separation_instance_formula source_replacement_instance_formula.
Theorem source_ordinal_collection_instances_formula_correct M rho ordinal phi n sep rep :
  holds M rho (source_ordinal_collection_instances_formula ordinal phi n sep rep) <->
  source_ordinal_collection_instances M (evalM M rho ordinal) (evalM M rho phi) (evalM M rho n)
    (evalM M rho sep) (evalM M rho rep).
Proof.
  unfold source_ordinal_collection_instances_formula,source_ordinal_collection_instances.
  setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_oc_form_formula_correct. setoid_rewrite source_separation_instance_formula_correct.
  setoid_rewrite source_replacement_instance_formula_correct.
  setoid_rewrite substitution_map_eval_succ.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_ordinal_collection_instances_total M ordinal phi n :
  source_bounded M ordinal (code_numeral M 1) -> source_bounded M phi (succM M (succM M n)) ->
  exists sep rep,source_ordinal_collection_instances M ordinal phi n sep rep.
Proof.
  intros HD HP. destruct (source_oc_form_total M ordinal phi) as [oc HO].
  destruct (numerical_separation_instance_total M phi (succM M n) HP) as [sep HS].
  destruct (numerical_replacement_instance_total M oc n (source_oc_form_bounded M ordinal phi oc n HD HP HO)) as [rep HR].
  exists sep,rep,oc. auto.
Qed.
Theorem source_ordinal_collection_instances_recognized M ordinal phi n sep rep :
  source_ordinal_collection_instances M ordinal phi n sep rep ->
  theory_axiom M ZFRSourceDescriptor sep /\ theory_axiom M ZFRSourceDescriptor rep.
Proof.
  intros [oc [HO [HS HR]]]. split.
  - exact (source_separation_instance_zfr_axiom M phi (succM M n) sep HS).
  - exact (source_replacement_instance_zfr_axiom M oc n rep HR).
Qed.

Print Assumptions source_oc_tail_formula_correct.
Print Assumptions source_oc_form_formula_correct.
Print Assumptions source_oc_form_total.
Print Assumptions source_oc_form_bounded.
Print Assumptions source_ordinal_collection_instances_formula_correct.
Print Assumptions source_ordinal_collection_instances_total.
Print Assumptions source_ordinal_collection_instances_recognized.

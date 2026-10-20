(** The exact repF, psiR, and psiS syntax recipes of Z_axL. The domain
    parameter will later be fixed to the pinned Lform. All matrix and
    parameter-count codes below range over arbitrary PA-model elements. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceRelativization SourceRelativizationBounds NumericalInstantiation
  SourceFiniteCutoffShift NumericalZFCAxioms NumericalZFCClosure NumericalCoreAxioms
  NumericalZFRAxioms NumericalTheories SourceSetTheoryDescriptors SchemaRenamingDescriptors
  SetSchemaConstructors NumericalSetClosure NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_l_repF M domain phi out := exists d0 d1 r guard,
  numerical_instantiation M domain (zeroM M) d0 /\
  numerical_instantiation M domain (code_numeral M 1) d1 /\
  source_relativization M domain phi r /\
  sf_relation M SFAnd d0 d1 guard /\ sf_relation M SFAnd guard r out.
Definition source_l_repF_formula (domain phi out:term) : form :=
  ∃∃∃∃ (numerical_instantiation_formula (lift4 domain) zero $3 ∧
    (numerical_instantiation_formula (lift4 domain) (num 1) $2 ∧
    (source_relativization_formula (lift4 domain) (lift4 phi) $1 ∧
    (sf_formula SFAnd $3 $2 $0 ∧ sf_formula SFAnd $0 $1 (lift4 out))))).
Local Opaque holds numerical_instantiation_formula source_relativization_formula sf_formula.

Theorem source_l_repF_formula_correct M rho domain phi out :
  holds M rho (source_l_repF_formula domain phi out) <->
  source_l_repF M (evalM M rho domain) (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_l_repF_formula,source_l_repF. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite numerical_instantiation_formula_correct.
  setoid_rewrite source_relativization_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,lift4. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_l_repF_total M domain phi : exists out,source_l_repF M domain phi out.
Proof.
  destruct (numerical_instantiation_total M domain (zeroM M)) as [d0 H0].
  destruct (numerical_instantiation_total M domain (code_numeral M 1)) as [d1 H1].
  destruct (source_relativization_total M domain phi) as [r HR].
  destruct (sf_relation_total M SFAnd d0 d1) as [guard HG].
  destruct (sf_relation_total M SFAnd guard r) as [out HO].
  exists out,d0,d1,r,guard. auto.
Qed.

Theorem source_l_repF_bounded M domain phi out n :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M phi (succM M (succM M n)) ->
  source_l_repF M domain phi out -> source_bounded M out (succM M (succM M n)).
Proof.
  intros HD HP (d0 & d1 & r & guard & H0 & H1 & HR & HG & HO).
  apply (proj2 (source_bounded_accept_binary M SFAnd guard r out (succM M (succM M n))
    (or_introl eq_refl) HO)). split.
  - apply (proj2 (source_bounded_accept_binary M SFAnd d0 d1 guard (succM M (succM M n))
      (or_introl eq_refl) HG)). split.
    + exact (numerical_instantiation_bounded M domain (zeroM M) d0 (succM M (succM M n))
        (sr_domain_bound_succ M domain (succM M (succM M n)) HD) (coding_zero_lt_succ M (succM M n)) H0).
    + exact (numerical_instantiation_bounded M domain (code_numeral M 1) d1 (succM M (succM M n))
        (sr_domain_bound_succ M domain (succM M (succM M n)) HD)
        (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M n)) (coding_zero_lt_succ M n)) H1).
  - exact (source_relativization_preserves_bound M phi domain (succM M (succM M n)) r HD HP HR).
Qed.

Definition source_l_psiR M phi out := exists shifted atom body,
  source_cutoff_shift M 2 phi shifted /\
  sf_relation M SFMember (zeroM M) (code_numeral M 2) atom /\
  sf_relation M SFAnd atom shifted body /\ sf_relation M SFEx body (zeroM M) out.
Definition source_l_psiR_formula (phi out:term) : form :=
  ∃∃∃ (source_cutoff_shift_formula 2 (lift3 phi) $2 ∧
    (sf_formula SFMember zero (num 2) $1 ∧
    (sf_formula SFAnd $1 $2 $0 ∧ sf_formula SFEx $0 zero (lift3 out)))).
Definition source_l_psiS M phi out := exists shifted atom,
  source_cutoff_shift M 1 phi shifted /\
  sf_relation M SFMember (zeroM M) (code_numeral M 1) atom /\ sf_relation M SFAnd atom shifted out.
Definition source_l_psiS_formula (phi out:term) : form :=
  ∃∃ (source_cutoff_shift_formula 1 (code_lift2 phi) $1 ∧
    (sf_formula SFMember zero (num 1) $0 ∧ sf_formula SFAnd $0 $1 (code_lift2 out))).
Local Opaque source_cutoff_shift_formula.

Theorem source_l_psiR_formula_correct M rho phi out :
  holds M rho (source_l_psiR_formula phi out) <->
  source_l_psiR M (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_l_psiR_formula,source_l_psiR. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite source_cutoff_shift_formula_correct.
  setoid_rewrite sf_formula_correct. unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_l_psiS_formula_correct M rho phi out :
  holds M rho (source_l_psiS_formula phi out) <->
  source_l_psiS M (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_l_psiS_formula,source_l_psiS. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite source_cutoff_shift_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Theorem source_l_psiR_total M phi : exists out,source_l_psiR M phi out.
Proof.
  destruct (source_cutoff_shift_total M 2 phi) as [shifted HS].
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 2)) as [atom HA].
  destruct (sf_relation_total M SFAnd atom shifted) as [body HB].
  destruct (sf_relation_total M SFEx body (zeroM M)) as [out HO].
  exists out,shifted,atom,body. auto.
Qed.
Theorem source_l_psiS_total M phi : exists out,source_l_psiS M phi out.
Proof.
  destruct (source_cutoff_shift_total M 1 phi) as [shifted HS].
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 1)) as [atom HA].
  destruct (sf_relation_total M SFAnd atom shifted) as [out HO].
  exists out,shifted,atom. auto.
Qed.

Theorem source_l_psiR_bounded M phi out n :
  source_bounded M phi (succM M (succM M n)) -> source_l_psiR M phi out ->
  source_bounded M out (succM M (succM M n)).
Proof.
  intros HP (shifted & atom & body & HS & HA & HB & HO).
  apply (proj2 (source_bounded_accept_unary M SFEx body out (succM M (succM M n)) (or_intror eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFAnd atom shifted body (succM M (succM M (succM M n)))
    (or_introl eq_refl) HB)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 2) atom
      (succM M (succM M (succM M n))) (or_introl eq_refl) HA)). split.
    + apply coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
  - exact (source_cutoff_shift_bounded M 2 phi shifted n HP HS).
Qed.
Theorem source_l_psiS_bounded M phi out n :
  source_bounded M phi (succM M n) -> source_l_psiS M phi out ->
  source_bounded M out (succM M (succM M n)).
Proof.
  intros HP (shifted & atom & HS & HA & HO).
  apply (proj2 (source_bounded_accept_binary M SFAnd atom shifted out (succM M (succM M n))
    (or_introl eq_refl) HO)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 1) atom
      (succM M (succM M n)) (or_introl eq_refl) HA)). split.
    + apply coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_zero_lt_succ.
  - exact (source_cutoff_shift_bounded M 1 phi shifted n HP HS).
Qed.

Definition source_l_repL_leading M domain phi n z := exists rep,
  source_l_repF M domain phi rep /\ numerical_replacement_instance M rep n z.
Definition source_l_repL_leading_formula (domain phi n z:term) : form :=
  ∃ (source_l_repF_formula domain`[↑] phi`[↑] $0 ∧
    ∃∃∃∃ (source_bounded_accept_formula $4 (σ (σ n`[↑]`[↑]`[↑]`[↑]`[↑])) ∧
      (SchemaRenamingDescriptors.schema_renaming_formula SchemaRenamingDescriptors.RepA $4 $3 ∧
      (SchemaRenamingDescriptors.schema_renaming_formula SchemaRenamingDescriptors.RepB $4 $2 ∧
      (SchemaRenamingDescriptors.schema_renaming_formula SchemaRenamingDescriptors.RepC $4 $1 ∧
      (SetSchemaConstructors.sf_replacement_constructor_formula $3 $2 $1 $0 ∧
       NumericalSetClosure.all_prefix_formula n`[↑]`[↑]`[↑]`[↑]`[↑] $0 z`[↑]`[↑]`[↑]`[↑]`[↑])))))).

Local Opaque source_l_repF_formula source_bounded_accept_formula schema_renaming_formula
  sf_replacement_constructor_formula all_prefix_formula.
Theorem source_l_repL_leading_formula_correct M rho domain phi n z :
  holds M rho (source_l_repL_leading_formula domain phi n z) <->
  source_l_repL_leading M (evalM M rho domain) (evalM M rho phi) (evalM M rho n) (evalM M rho z).
Proof.
  unfold source_l_repL_leading_formula,source_l_repL_leading,numerical_replacement_instance.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_l_repF_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite schema_renaming_formula_correct.
  setoid_rewrite sf_replacement_constructor_correct.
  setoid_rewrite all_prefix_formula_correct.
  repeat setoid_rewrite substitution_map_eval_succ.
  unfold evalM. repeat setoid_rewrite eval_up. split.
  - intros (rep & HR & a & b & c & o & HB & HA & HB' & HC & HO & HZ).
    exists rep. split;[exact HR|]. split;[exact HB|]. exists a,b,c,o.
    exact (conj HA (conj HB' (conj HC (conj HO HZ)))).
  - intros (rep & HR & HB & a & b & c & o & HA & HB' & HC & HO & HZ).
    exists rep. split;[exact HR|]. exists a,b,c,o.
    exact (conj HB (conj HA (conj HB' (conj HC (conj HO HZ))))).
Qed.

Theorem source_l_repL_leading_total M domain phi n :
  source_bounded M domain (code_numeral M 1) -> source_bounded M phi (succM M (succM M n)) ->
  exists z,source_l_repL_leading M domain phi n z.
Proof.
  intros HD HP. destruct (source_l_repF_total M domain phi) as [rep HR].
  destruct (numerical_replacement_instance_total M rep n (source_l_repF_bounded M domain phi rep n HD HP HR)) as [z HZ].
  exists z,rep. auto.
Qed.

Theorem source_l_repL_leading_recognized M domain phi n z :
  source_l_repL_leading M domain phi n z -> theory_axiom M ZFRSourceDescriptor z.
Proof.
  intros [rep [HR HZ]]. apply ZFRSourceDescriptor_axiom. left. right. right.
  split;[exact (numerical_replacement_instance_closed M rep n z HZ)|]. now exists rep,n.
Qed.

Print Assumptions source_l_repF_formula_correct.
Print Assumptions source_l_repF_total.
Print Assumptions source_l_repF_bounded.
Print Assumptions source_l_psiR_formula_correct.
Print Assumptions source_l_psiS_formula_correct.
Print Assumptions source_l_psiR_total.
Print Assumptions source_l_psiS_total.
Print Assumptions source_l_psiR_bounded.
Print Assumptions source_l_psiS_bounded.
Print Assumptions source_l_repL_leading_total.
Print Assumptions source_l_repL_leading_formula_correct.
Print Assumptions source_l_repL_leading_recognized.

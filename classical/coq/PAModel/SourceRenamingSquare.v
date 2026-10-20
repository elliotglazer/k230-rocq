(** Arithmetic commuting squares between two source renamings and two
    capture-avoiding variable substitutions. All maps are actual numerical graphs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps
  NumericalSubstitution SetFormulaCodes SetCodeDescent SourceBounded RenamingPayloads SubstitutionPayloads.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_map_square M sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k :=
  forall i j l m,coding_lt M i k -> substitution_lookup M sb sc sn sbase i j ->
    renaming_lookup M tb tc tn tdelta j m -> renaming_lookup M rb rc rn rdelta i l ->
    substitution_lookup M ub uc un ubase l m.
Definition square_lift4 (t:term) := t`[↑]`[↑]`[↑]`[↑].
Lemma square_eval_lift4 M rho a b c d t :
  evalM M (a .: b .: c .: d .: rho) (square_lift4 t)=evalM M rho t.
Proof. unfold square_lift4,evalM. now rewrite !eval_up. Qed.
Definition source_map_square_formula
    (sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k:term) : form :=
  ∀∀∀∀ (Peano.sless $3 (square_lift4 k) →
    substitution_lookup_formula (square_lift4 sb) (square_lift4 sc) (square_lift4 sn) (square_lift4 sbase) $3 $2 →
    renaming_lookup_formula (square_lift4 tb) (square_lift4 tc) (square_lift4 tn) (square_lift4 tdelta) $2 $0 →
    renaming_lookup_formula (square_lift4 rb) (square_lift4 rc) (square_lift4 rn) (square_lift4 rdelta) $3 $1 →
    substitution_lookup_formula (square_lift4 ub) (square_lift4 uc) (square_lift4 un) (square_lift4 ubase) $1 $0).
Local Opaque holds substitution_lookup_formula renaming_lookup_formula.
Lemma source_map_square_formula_correct M rho sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k :
  holds M rho (source_map_square_formula sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k) <->
  source_map_square M (evalM M rho sb) (evalM M rho sc) (evalM M rho sn) (evalM M rho sbase)
    (evalM M rho rb) (evalM M rho rc) (evalM M rho rn) (evalM M rho rdelta)
    (evalM M rho tb) (evalM M rho tc) (evalM M rho tn) (evalM M rho tdelta)
    (evalM M rho ub) (evalM M rho uc) (evalM M rho un) (evalM M rho ubase) (evalM M rho k).
Proof.
  unfold source_map_square_formula,source_map_square.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite renaming_lookup_formula_correct. setoid_rewrite square_eval_lift4. reflexivity.
Qed.

Theorem source_map_square_lift M sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k
    sd se sm rd re rm td te tm ud ue um :
  source_map_square M sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k ->
  substitution_lift M sb sc sn sbase sd se sm -> renaming_lift M rb rc rn rdelta rd re rm ->
  renaming_lift M tb tc tn tdelta td te tm -> substitution_lift M ub uc un ubase ud ue um ->
  source_map_square M sd se sm (succM M sbase) rd re rm rdelta td te tm tdelta
    ud ue um (succM M ubase) (succM M k).
Proof.
  intros HSquare HS HR HT HU i j l m HI HSI HTJ HRI.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - apply (proj1 (substitution_lift_head M sb sc sn sbase sd se sm j HS)) in HSI. subst j.
    apply (proj1 (renaming_lift_head M tb tc tn tdelta td te tm m HT)) in HTJ. subst m.
    apply (proj1 (renaming_lift_head M rb rc rn rdelta rd re rm l HR)) in HRI. subst l.
    exact (proj2 (substitution_lift_head M ub uc un ubase ud ue um (zeroM M) HU) eq_refl).
  - destruct (substitution_lift_tail_inv M sb sc sn sbase sd se sm i' j HS HSI) as [j' [HSI' EJ]]. subst j.
    destruct (renaming_lift_tail_inv M tb tc tn tdelta td te tm j' m HT HTJ) as [m' [HTJ' EM]]. subst m.
    destruct (renaming_lift_tail_inv M rb rc rn rdelta rd re rm i' l HR HRI) as [l' [HRI' EL]]. subst l.
    apply (proj2 (substitution_lift_tail M ub uc un ubase ud ue um l' m' HU)).
    exact (HSquare i' j' l' m' (proj1 (coding_lt_succ_cancel M i' k) HI) HSI' HTJ' HRI').
Qed.

Definition source_renaming_square_at M f :=
  forall k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v,
  source_bounded M f k -> numerical_substitution M f sb sc sn sbase fs ->
  numerical_renaming M f rb rc rn rdelta fr -> numerical_renaming M fs tb tc tn tdelta v ->
  source_map_square M sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase k ->
  numerical_substitution M fr ub uc un ubase v.
Definition source_renaming_square_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀ (source_bounded_accept_formula $20 $19 →
    numerical_substitution_formula $20 $18 $17 $16 $15 $2 →
    numerical_renaming_formula $20 $14 $13 $12 $11 $1 →
    numerical_renaming_formula $2 $10 $9 $8 $7 $0 →
    source_map_square_formula $18 $17 $16 $15 $14 $13 $12 $11 $10 $9 $8 $7 $6 $5 $4 $3 $19 →
    numerical_substitution_formula $1 $6 $5 $4 $3 $0).
Local Opaque source_bounded_accept_formula numerical_substitution_formula numerical_renaming_formula source_map_square_formula.
Theorem source_renaming_square_definable M : Definable1 M (source_renaming_square_at M).
Proof.
  exists source_renaming_square_formula,(fun _=>zeroM M). intro f.
  unfold source_renaming_square_formula,source_renaming_square_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_map_square_formula_correct. reflexivity.
Qed.

Theorem numerical_source_renaming_square M f : source_renaming_square_at M f.
Proof.
  revert f. apply (sf_code_induction M (source_renaming_square_at M)).
  - apply source_renaming_square_definable.
  - intros k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v HB HS HR HT HQ.
    apply (proj1 (numerical_substitution_invalid M (zeroM M) sb sc sn sbase fs (or_introl eq_refl))) in HS. subst fs.
    apply (proj1 (numerical_renaming_invalid M (zeroM M) rb rc rn rdelta fr (or_introl eq_refl))) in HR. subst fr.
    apply (proj1 (numerical_renaming_invalid M (zeroM M) tb tc tn tdelta v (or_introl eq_refl))) in HT. subst v.
    apply (proj2 (numerical_substitution_invalid M (zeroM M) ub uc un ubase (zeroM M) (or_introl eq_refl))). reflexivity.
  - intros f HBad k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v HB.
    exfalso. exact (source_bounded_reject_invalid M f k HBad HB).
  - intros a d f HShape k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v HB HS HR HT HQ.
    destruct (proj1 (source_bounded_accept_atom M SFMember a d f k (or_introl eq_refl) HShape) HB) as [HA HD].
    destruct (proj1 (numerical_substitution_member M a d f sb sc sn sbase fs HShape) HS) as (as' & ds' & HSA & HSD & HFS).
    destruct (proj1 (numerical_renaming_member M as' ds' fs tb tc tn tdelta v HFS) HT) as (av & dv & HTA & HTD & HV).
    destruct (proj1 (numerical_renaming_member M a d f rb rc rn rdelta fr HShape) HR) as (ar & dr & HRA & HRD & HFR).
    apply (proj2 (numerical_substitution_member M ar dr fr ub uc un ubase v HFR)).
    exists av,dv. split;[exact (HQ a as' ar av HA HSA HTA HRA)|].
    split;[exact (HQ d ds' dr dv HD HSD HTD HRD)|exact HV].
  - intros a d f HShape k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v HB HS HR HT HQ.
    destruct (proj1 (source_bounded_accept_atom M SFEqual a d f k (or_intror eq_refl) HShape) HB) as [HA HD].
    destruct (proj1 (numerical_substitution_equal M a d f sb sc sn sbase fs HShape) HS) as (as' & ds' & HSA & HSD & HFS).
    destruct (proj1 (numerical_renaming_equal M as' ds' fs tb tc tn tdelta v HFS) HT) as (av & dv & HTA & HTD & HV).
    destruct (proj1 (numerical_renaming_equal M a d f rb rc rn rdelta fr HShape) HR) as (ar & dr & HRA & HRD & HFR).
    apply (proj2 (numerical_substitution_equal M ar dr fr ub uc un ubase v HFR)).
    exists av,dv. split;[exact (HQ a as' ar av HA HSA HTA HRA)|].
    split;[exact (HQ d ds' dr dv HD HSD HTD HRD)|exact HV].
  - intros h a d f HH HShape IHA IHD k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v HB HS HR HT HQ.
    destruct (proj1 (source_bounded_accept_binary M h a d f k HH HShape) HB) as [HA HD].
    destruct (proj1 (numerical_substitution_binary M h a d f sb sc sn sbase fs HH HShape) HS) as (as' & ds' & HSA & HSD & HFS).
    destruct (proj1 (numerical_renaming_binary M h as' ds' fs tb tc tn tdelta v HH HFS) HT) as (av & dv & HTA & HTD & HV).
    destruct (proj1 (numerical_renaming_binary M h a d f rb rc rn rdelta fr HH HShape) HR) as (ar & dr & HRA & HRD & HFR).
    apply (proj2 (numerical_substitution_binary M h ar dr fr ub uc un ubase v HH HFR)).
    exists av,dv. split;[exact (IHA k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase as' ar av HA HSA HRA HTA HQ)|].
    split;[exact (IHD k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase ds' dr dv HD HSD HRD HTD HQ)|exact HV].
  - intros h a f HH HShape IH k sb sc sn sbase rb rc rn rdelta tb tc tn tdelta ub uc un ubase fs fr v HB HS HR HT HQ.
    pose proof (proj1 (source_bounded_accept_unary M h a f k HH HShape) HB) as HA.
    assert (HUniv:exists universal,h=renaming_source_quantifier universal).
    { destruct HH as [E|E];subst h;[exists true|exists false];reflexivity. }
    destruct HUniv as [universal E]. subst h.
    assert (HShapeS:sf_relation M (substitution_source_quantifier universal) a (zeroM M) f) by (destruct universal;exact HShape).
    destruct (proj1 (numerical_substitution_quantifier M universal a f sb sc sn sbase fs HShapeS) HS)
      as (sd & se & sm & as' & HSL & HSA & HFS).
    destruct (proj1 (numerical_renaming_quantifier M universal a f rb rc rn rdelta fr HShape) HR)
      as (rd & re & rm & ar & HRL & HRA & HFR).
    assert (HFST:sf_relation M (renaming_source_quantifier universal) as' (zeroM M) fs) by (destruct universal;exact HFS).
    destruct (proj1 (numerical_renaming_quantifier M universal as' fs tb tc tn tdelta v HFST) HT)
      as (td & te & tm & av & HTL & HTA & HV).
    destruct (substitution_lift_total M ub uc un ubase) as (ud & ue & um & HUL).
    assert (HFRS:sf_relation M (substitution_source_quantifier universal) ar (zeroM M) fr) by (destruct universal;exact HFR).
    apply (proj2 (numerical_substitution_quantifier M universal ar fr ub uc un ubase v HFRS)).
    exists ud,ue,um,av. split;[exact HUL|]. split;[|destruct universal;exact HV].
    apply (IH (succM M k) sd se sm (succM M sbase) rd re rm rdelta
      td te tm tdelta ud ue um (succM M ubase) as' ar av HA HSA HRA HTA).
    exact (source_map_square_lift M sb sc sn sbase rb rc rn rdelta tb tc tn tdelta
      ub uc un ubase k sd se sm rd re rm td te tm ud ue um HQ HSL HRL HTL HUL).
Qed.

Print Assumptions source_map_square_formula_correct.
Print Assumptions source_map_square_lift.
Print Assumptions source_renaming_square_definable.
Print Assumptions numerical_source_renaming_square.

(** Composition of two actual numerical source substitutions, agreeing on an arbitrary internally coded free-variable bound. Binder lifting applies to all three maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs NumericalEnvironments NumericalContextRenaming
  SetFormulaCodes SetCodeDescent SourceBounded NumericalSubstitutionMaps
  NumericalSubstitution SubstitutionPayloads NumericalRenamingMaps NumericalRenaming.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_composition_agrees M ab ac an abase rb rc rn rbase cb cc cn cbase k :=
  forall i j v,coding_lt M i k -> substitution_lookup M ab ac an abase i j ->
    substitution_lookup M rb rc rn rbase j v -> substitution_lookup M cb cc cn cbase i v.

Definition substitution_composition_agrees_formula
    (ab ac an abase rb rc rn rbase cb cc cn cbase k : term) : form :=
  ∀∀∀ (Peano.sless $2 (context_lift3 k) →
    substitution_lookup_formula (context_lift3 ab) (context_lift3 ac)
      (context_lift3 an) (context_lift3 abase) $2 $1 →
    substitution_lookup_formula (context_lift3 rb) (context_lift3 rc)
      (context_lift3 rn) (context_lift3 rbase) $1 $0 →
    substitution_lookup_formula (context_lift3 cb) (context_lift3 cc)
      (context_lift3 cn) (context_lift3 cbase) $2 $0).

Local Opaque holds substitution_lookup_formula.
Lemma substitution_composition_agrees_formula_correct M rho
    ab ac an abase rb rc rn rbase cb cc cn cbase k :
  holds M rho (substitution_composition_agrees_formula ab ac an abase rb rc rn rbase cb cc cn cbase k) <->
  substitution_composition_agrees M (evalM M rho ab) (evalM M rho ac)
    (evalM M rho an) (evalM M rho abase) (evalM M rho rb) (evalM M rho rc)
    (evalM M rho rn) (evalM M rho rbase) (evalM M rho cb) (evalM M rho cc)
    (evalM M rho cn) (evalM M rho cbase) (evalM M rho k).
Proof.
  unfold substitution_composition_agrees_formula,substitution_composition_agrees.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite context_eval_lift3. reflexivity.
Qed.

Lemma substitution_composition_agrees_lift M ab ac an abase rb rc rn rbase cb cc cn cbase
    ad ae am rd re rm cd ce cm k :
  substitution_composition_agrees M ab ac an abase rb rc rn rbase cb cc cn cbase k ->
  substitution_lift M ab ac an abase ad ae am ->
  substitution_lift M rb rc rn rbase rd re rm ->
  substitution_lift M cb cc cn cbase cd ce cm ->
  substitution_composition_agrees M ad ae am (succM M abase) rd re rm (succM M rbase)
    cd ce cm (succM M cbase) (succM M k).
Proof.
  intros HA HLA HLR HLC i j v HI HS HR.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - apply (proj1 (substitution_lift_head M ab ac an abase ad ae am j HLA)) in HS.
    subst j. apply (proj1 (substitution_lift_head M rb rc rn rbase rd re rm v HLR)) in HR.
    subst v. exact (proj2 (substitution_lift_head M cb cc cn cbase cd ce cm (zeroM M) HLC) eq_refl).
  - destruct (substitution_lift_tail_inv M ab ac an abase ad ae am i' j HLA HS)
      as [j' [HS' EJ]]. subst j.
    destruct (substitution_lift_tail_inv M rb rc rn rbase rd re rm j' v HLR HR)
      as [v' [HR' EV]]. subst v.
    apply (proj2 (substitution_lift_tail M cb cc cn cbase cd ce cm i' v' HLC)).
    exact (HA i' j' v' (proj1 (coding_lt_succ_cancel M i' k) HI) HS' HR').
Qed.

Definition source_substitution_composition_property M f :=
  forall k ab ac an abase rb rc rn rbase cb cc cn cbase g h,
    source_bounded M f k -> numerical_substitution M f ab ac an abase g ->
    numerical_substitution M g rb rc rn rbase h ->
    substitution_composition_agrees M ab ac an abase rb rc rn rbase cb cc cn cbase k ->
    numerical_substitution M f cb cc cn cbase h.

Definition source_substitution_composition_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀ (source_bounded_accept_formula $15 $14 →
    numerical_substitution_formula $15 $13 $12 $11 $10 $1 →
    numerical_substitution_formula $1 $9 $8 $7 $6 $0 →
    substitution_composition_agrees_formula $13 $12 $11 $10 $9 $8 $7 $6 $5 $4 $3 $2 $14 →
    numerical_substitution_formula $15 $5 $4 $3 $2 $0).

Local Opaque source_bounded_accept_formula numerical_substitution_formula
  substitution_composition_agrees_formula.
Lemma source_substitution_composition_definable M :
  Definable1 M (source_substitution_composition_property M).
Proof.
  exists source_substitution_composition_formula,(fun _=>zeroM M). intro f.
  unfold source_substitution_composition_formula,source_substitution_composition_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite substitution_composition_agrees_formula_correct. reflexivity.
Qed.

Theorem numerical_substitution_composition M f : source_substitution_composition_property M f.
Proof.
  revert f. apply (sf_code_induction M (source_substitution_composition_property M)).
  - apply source_substitution_composition_definable.
  - intros k ab ac an abase rb rc rn rbase cb cc cn cbase g h _ HS HR _.
    apply (proj1 (numerical_substitution_invalid M (zeroM M) ab ac an abase g (or_introl eq_refl))) in HS.
    subst g. apply (proj1 (numerical_substitution_invalid M (zeroM M) rb rc rn rbase h (or_introl eq_refl))) in HR.
    subst h. apply (proj2 (numerical_substitution_invalid M (zeroM M) cb cc cn cbase
      (zeroM M) (or_introl eq_refl))). reflexivity.
  - intros f Hbad k ab ac an abase rb rc rn rbase cb cc cn cbase g h HF _ _ _.
    exfalso. exact (source_bounded_reject_invalid M f k Hbad HF).
  - intros x y f Hf k ab ac an abase rb rc rn rbase cb cc cn cbase g h HF HS HR HA.
    destruct (proj1 (source_bounded_accept_atom M SFMember x y f k (or_introl eq_refl) Hf) HF) as [HX HY].
    destruct (proj1 (numerical_substitution_member M x y f ab ac an abase g Hf) HS)
      as [x' [y' [HSX [HSY HG]]]].
    destruct (proj1 (numerical_substitution_member M x' y' g rb rc rn rbase h HG) HR)
      as [x'' [y'' [HRX [HRY HH]]]].
    apply (proj2 (numerical_substitution_member M x y f cb cc cn cbase h Hf)).
    exists x'',y''. split;[exact (HA x x' x'' HX HSX HRX)|].
    split;[exact (HA y y' y'' HY HSY HRY)|exact HH].
  - intros x y f Hf k ab ac an abase rb rc rn rbase cb cc cn cbase g h HF HS HR HA.
    destruct (proj1 (source_bounded_accept_atom M SFEqual x y f k (or_intror eq_refl) Hf) HF) as [HX HY].
    destruct (proj1 (numerical_substitution_equal M x y f ab ac an abase g Hf) HS)
      as [x' [y' [HSX [HSY HG]]]].
    destruct (proj1 (numerical_substitution_equal M x' y' g rb rc rn rbase h HG) HR)
      as [x'' [y'' [HRX [HRY HH]]]].
    apply (proj2 (numerical_substitution_equal M x y f cb cc cn cbase h Hf)).
    exists x'',y''. split;[exact (HA x x' x'' HX HSX HRX)|].
    split;[exact (HA y y' y'' HY HSY HRY)|exact HH].
  - intros hd x y f Hhd Hf IHX IHY k ab ac an abase rb rc rn rbase cb cc cn cbase g h HF HS HR HA.
    destruct (proj1 (source_bounded_accept_binary M hd x y f k Hhd Hf) HF) as [HX HY].
    destruct (proj1 (numerical_substitution_binary M hd x y f ab ac an abase g Hhd Hf) HS)
      as [x' [y' [HSX [HSY HG]]]].
    destruct (proj1 (numerical_substitution_binary M hd x' y' g rb rc rn rbase h Hhd HG) HR)
      as [x'' [y'' [HRX [HRY HH]]]].
    apply (proj2 (numerical_substitution_binary M hd x y f cb cc cn cbase h Hhd Hf)).
    exists x'',y''. split;[exact (IHX k ab ac an abase rb rc rn rbase cb cc cn cbase x' x'' HX HSX HRX HA)|].
    split;[exact (IHY k ab ac an abase rb rc rn rbase cb cc cn cbase y' y'' HY HSY HRY HA)|exact HH].
  - intros hd x f Hhd Hf IH k ab ac an abase rb rc rn rbase cb cc cn cbase g h HF HS HR HA.
    pose proof (proj1 (source_bounded_accept_unary M hd x f k Hhd Hf) HF) as HX.
    assert (Hex:exists universal,hd=substitution_source_quantifier universal).
    { destruct Hhd as [E|E];subst hd;[exists true|exists false];reflexivity. }
    destruct Hex as [universal E]. subst hd.
    destruct (proj1 (numerical_substitution_quantifier M universal x f ab ac an abase g Hf) HS)
      as [ad [ae [am [x' [HLA [HSX HG]]]]]].
    destruct (proj1 (numerical_substitution_quantifier M universal x' g rb rc rn rbase h HG) HR)
      as [rd [re [rm [x'' [HLR [HRX HH]]]]]].
    destruct (substitution_lift_total M cb cc cn cbase) as [cd [ce [cm HLC]]].
    apply (proj2 (numerical_substitution_quantifier M universal x f cb cc cn cbase h Hf)).
    exists cd,ce,cm,x''. split;[exact HLC|]. split;[|exact HH].
    apply (IH (succM M k) ad ae am (succM M abase) rd re rm (succM M rbase)
      cd ce cm (succM M cbase) x' x'' HX HSX HRX).
    exact (substitution_composition_agrees_lift M ab ac an abase rb rc rn rbase cb cc cn cbase
      ad ae am rd re rm cd ce cm k HA HLA HLR HLC).
Qed.

Print Assumptions numerical_substitution_composition.


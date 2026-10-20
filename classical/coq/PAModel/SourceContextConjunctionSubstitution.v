(** Conjunction folding commutes with the actual numerical source
    renaming of every row of an internally finite context table. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs ProofClosure
  SetFormulaCodes NumericalContexts NumericalContextRenaming NumericalSubstitution SourceContextConjunction.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_substitution M b c n p q m delta d e :=
  forall i f g, coding_lt M i n -> beta M b c i f -> beta M d e i g ->
    numerical_substitution M f p q m delta g.

Definition source_context_substitution_formula (b c n p q m delta d e : term) : form :=
  ∀∀∀ (Peano.sless $2 (context_lift3 n) →
    beta_formula (context_lift3 b) (context_lift3 c) $2 $1 →
    beta_formula (context_lift3 d) (context_lift3 e) $2 $0 →
    numerical_substitution_formula $1 (context_lift3 p) (context_lift3 q)
      (context_lift3 m) (context_lift3 delta) $0).

Local Opaque holds beta_formula numerical_substitution_formula.
Theorem source_context_substitution_formula_correct M rho b c n p q m delta d e :
  holds M rho (source_context_substitution_formula b c n p q m delta d e) <->
  source_context_substitution M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho p) (evalM M rho q) (evalM M rho m) (evalM M rho delta)
    (evalM M rho d) (evalM M rho e).
Proof.
  unfold source_context_substitution_formula,source_context_substitution.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite context_eval_lift3. reflexivity.
Qed.


Definition source_context_conjunction_substitution_at M sb sc tb tc rb rc rn delta n :=forall f g,
  source_context_conjunction M sb sc n f ->source_context_conjunction M tb tc n g ->
  source_context_substitution M sb sc n rb rc rn delta tb tc ->numerical_substitution M f rb rc rn delta g.
Definition source_context_conjunction_substitution_formula :form :=
  ∀∀ (source_context_conjunction_formula $3 $4 $2 $1 →
    source_context_conjunction_formula $5 $6 $2 $0 →
    source_context_substitution_formula $3 $4 $2 $7 $8 $9 $10 $5 $6 →
    numerical_substitution_formula $1 $7 $8 $9 $10 $0).
Local Opaque holds source_context_conjunction_formula source_context_substitution_formula numerical_substitution_formula.
Lemma source_context_conjunction_substitution_definable M sb sc tb tc rb rc rn delta :
  Definable1 M (source_context_conjunction_substitution_at M sb sc tb tc rb rc rn delta).
Proof.
  exists source_context_conjunction_substitution_formula,
    (sb .: sc .: tb .: tc .: rb .: rc .: rn .: delta .: fun _=>zeroM M). intro n.
  unfold source_context_conjunction_substitution_at,source_context_conjunction_substitution_formula.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_context_conjunction_formula_correct.
  setoid_rewrite source_context_substitution_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct. reflexivity.
Qed.

Theorem source_context_conjunction_substitution M sb sc tb tc rb rc rn delta :
  forall n,source_context_conjunction_substitution_at M sb sc tb tc rb rc rn delta n.
Proof.
  apply (definable_induction M (source_context_conjunction_substitution_at M sb sc tb tc rb rc rn delta)
    (source_context_conjunction_substitution_definable M sb sc tb tc rb rc rn delta)).
  - intros f g HF HG HCtx. apply source_context_conjunction_zero in HF.
    apply source_context_conjunction_zero in HG.
    apply (proj2 (numerical_substitution_binary M SFImpl (zeroM M)(zeroM M) f rb rc rn delta g
      (or_intror (or_intror eq_refl)) HF)).
    exists (zeroM M),(zeroM M). split;[|split;[|exact HG]];
      apply (proj2 (numerical_substitution_invalid M (zeroM M) rb rc rn delta (zeroM M) (or_introl eq_refl)));reflexivity.
  - intros n IH f g HF HG HCtx.
    apply source_context_conjunction_succ in HF. apply source_context_conjunction_succ in HG.
    destruct HF as [p [h [HP [HH HAnd]]]];destruct HG as [q [j [HQ [HJ HAnd']]]].
    apply (proj2 (numerical_substitution_binary M SFAnd p h f rb rc rn delta g (or_introl eq_refl) HAnd)).
    exists q,j. split.
    + apply (IH p q HP HQ). intros i a b HI HA HB.
      exact (HCtx i a b (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n)) HA HB).
    + split;[exact (HCtx n h j (coding_lt_succ M n) HH HJ)|exact HAnd'].
Qed.

Print Assumptions source_context_conjunction_substitution_definable.
Print Assumptions source_context_conjunction_substitution.

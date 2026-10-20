(** The exact pcs membership recipe: each quantified body contributes its
    domain relativization and negation, paired with its context bound. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs Pairing
  SetFormulaCodes SetCodeDescent SourceBounded SourceRelativization SourceRelativizationBounds
  SourceRelativizationFunctionality SourceQuantifierPieceRules SourceQuantifierPieces SourceQuantifierPieceInversion.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_pcs_sign M domain body piece :=
  source_relativization M domain body piece \/ exists r,
    source_relativization M domain body r /\ sf_relation M SFImpl r (zeroM M) piece.
Definition source_pcs_sign_formula (domain body piece:term) : form :=
  source_relativization_formula domain body piece ∨
  ∃ (source_relativization_formula domain`[↑] body`[↑] $0 ∧ sf_formula SFImpl $0 zero piece`[↑]).
Definition source_pcs_entry M domain f n entry := exists k body piece,
  source_quantifier_body M f n k body /\ source_pcs_sign M domain body piece /\ pair_graph M k piece entry.
Definition source_pcs_entry_formula (domain f n entry:term) : form :=
  ∃∃∃ (source_quantifier_body_formula (lift3 f) (lift3 n) $2 $1 ∧
    (source_pcs_sign_formula (lift3 domain) $1 $0 ∧ pair_formula $2 $0 (lift3 entry))).
Local Opaque holds source_relativization_formula sf_formula source_quantifier_body_formula pair_formula.

Theorem source_pcs_sign_formula_correct M rho domain body piece :
  holds M rho (source_pcs_sign_formula domain body piece) <->
  source_pcs_sign M (evalM M rho domain) (evalM M rho body) (evalM M rho piece).
Proof.
  unfold source_pcs_sign_formula,source_pcs_sign. rewrite holds_or.
  setoid_rewrite holds_ex. setoid_rewrite holds_and. setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite sf_formula_correct. unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.
Local Opaque source_pcs_sign_formula.
Theorem source_pcs_entry_formula_correct M rho domain f n entry :
  holds M rho (source_pcs_entry_formula domain f n entry) <->
  source_pcs_entry M (evalM M rho domain) (evalM M rho f) (evalM M rho n) (evalM M rho entry).
Proof.
  unfold source_pcs_entry_formula,source_pcs_entry. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite source_quantifier_body_formula_correct.
  setoid_rewrite source_pcs_sign_formula_correct. setoid_rewrite pair_formula_correct.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_pcs_sign_bounded M domain body piece k :
  source_bounded M domain (code_numeral M 1) -> source_bounded M body k ->
  source_pcs_sign M domain body piece -> source_bounded M piece k.
Proof.
  intros HD HB [HR|[r [HR HN]]].
  - exact (source_relativization_preserves_bound M body domain k piece HD HB HR).
  - apply (proj2 (source_bounded_accept_binary M SFImpl r (zeroM M) piece k
      (or_intror (or_intror eq_refl)) HN)). split.
    + exact (source_relativization_preserves_bound M body domain k r HD HB HR).
    + apply source_bounded_accept_falsity.
Qed.

Theorem source_pcs_entry_bounded M domain f n entry :
  source_bounded M domain (code_numeral M 1) -> source_bounded M f n ->
  source_pcs_entry M domain f n entry -> exists k piece,
    pair_graph M k piece entry /\ source_bounded M piece (succM M k).
Proof.
  intros HD HF (k & body & piece & HP & HS & HE). exists k,piece. split;[exact HE|].
  exact (source_pcs_sign_bounded M domain body piece (succM M k) HD
    (source_quantifier_body_bounded M f n k body HP HF) HS).
Qed.

Theorem source_pcs_entry_binary M domain h a b f n entry :
  sf_binary h -> sf_relation M h a b f ->
  (source_pcs_entry M domain f n entry <->
   source_pcs_entry M domain a n entry \/ source_pcs_entry M domain b n entry).
Proof.
  intros HH HF. split.
  - intros (k & body & piece & HP & HS & HE).
    apply (proj1 (source_quantifier_body_binary M h a b f n k body HH HF)) in HP.
    destruct HP as [HP|HP];[left|right];exists k,body,piece;auto.
  - intros [(k & body & piece & HP & HS & HE)|(k & body & piece & HP & HS & HE)].
    + exists k,body,piece. split;[apply (proj2 (source_quantifier_body_binary M h a b f n k body HH HF));auto|auto].
    + exists k,body,piece. split;[apply (proj2 (source_quantifier_body_binary M h a b f n k body HH HF));auto|auto].
Qed.

Theorem source_pcs_entry_quantifier M domain h a f n rel neg posentry negentry entry :
  (h=SFAll \/ h=SFEx) -> sf_relation M h a (zeroM M) f ->
  source_relativization M domain a rel -> sf_relation M SFImpl rel (zeroM M) neg ->
  pair_graph M n rel posentry -> pair_graph M n neg negentry ->
  (source_pcs_entry M domain f n entry <->
   entry=posentry \/ entry=negentry \/ source_pcs_entry M domain a (succM M n) entry).
Proof.
  intros HH HF HR HN HEPos HENeg. split.
  - intros (k & body & piece & HP & HS & HE).
    apply (proj1 (source_quantifier_body_quantifier M h a f n k body HH HF)) in HP.
    destruct HP as [[-> ->]|HP].
    + destruct HS as [HS|[r [HS HNeg]]].
      * assert (E:piece=rel) by (exact (source_relativization_functional M a domain piece rel HS HR)).
        subst piece. left. exact (pair_functional M n rel entry posentry HE HEPos).
      * assert (E:r=rel) by (exact (source_relativization_functional M a domain r rel HS HR)). subst r.
        assert (E:piece=neg) by (exact (sf_relation_functional M SFImpl rel (zeroM M) piece neg HNeg HN)).
        subst piece. right;left. exact (pair_functional M n neg entry negentry HE HENeg).
    + right;right. exists k,body,piece. auto.
  - intros [->|[->|HP]].
    + exists n,a,rel. split.
      * apply (proj2 (source_quantifier_body_quantifier M h a f n n a HH HF)). left. auto.
      * split;[now left|exact HEPos].
    + exists n,a,neg. split.
      * apply (proj2 (source_quantifier_body_quantifier M h a f n n a HH HF)). left. auto.
      * split;[right;now exists rel|exact HENeg].
    + destruct HP as (k & body & piece & HP & HS & HE). exists k,body,piece. split.
      * apply (proj2 (source_quantifier_body_quantifier M h a f n k body HH HF)). now right.
      * auto.
Qed.

Theorem source_pcs_entry_leaf_none M domain f n entry :
  (f=zeroM M \/ sf_invalid M f \/ exists h a b,(h=SFMember \/ h=SFEqual) /\ sf_relation M h a b f) ->
  ~source_pcs_entry M domain f n entry.
Proof.
  intros HF (k & body & piece & HP & HS & HE).
  exact (source_quantifier_body_leaf_none M f n k body HF HP).
Qed.

Print Assumptions source_pcs_sign_formula_correct.
Print Assumptions source_pcs_entry_formula_correct.
Print Assumptions source_pcs_entry_bounded.
Print Assumptions source_pcs_entry_binary.
Print Assumptions source_pcs_entry_quantifier.

(** Arbitrary internally finite piece tables retain the free-name bound
    of their ordinal and container roles. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  Pairing SetFormulaCodes SourceBounded NumericalContexts SourcePieceClosure SourcePieceConjunction
  SourcePieceConjunctionFormula SourcePCSPieces SourcePCSTables.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_piece_table_valid M sb sc n:=forall entry count phi,
  context_member M sb sc n entry ->pair_graph M count phi entry ->source_bounded M phi(succM M count).
Definition source_piece_table_valid_formula(sb sc n:term):form:=
  ∀∀∀(context_member_formula(lift3 sb)(lift3 sc)(lift3 n)$2 →pair_formula $1 $0 $2 →
    source_bounded_accept_formula $0(σ $1)).
Local Opaque holds context_member_formula pair_formula source_bounded_accept_formula.
Theorem source_piece_table_valid_formula_correct M rho sb sc n:
  holds M rho(source_piece_table_valid_formula sb sc n) <->
  source_piece_table_valid M(evalM M rho sb)(evalM M rho sc)(evalM M rho n).
Proof.
  unfold source_piece_table_valid_formula,source_piece_table_valid.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite pair_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_pcs_table_valid M domain f count sb sc n:
  source_bounded M domain(code_numeral M 1) ->source_bounded M f count ->
  source_pcs_table M domain f count sb sc n ->source_piece_table_valid M sb sc n.
Proof.
  intros HD HF HT entry k phi HE HP.
  destruct(source_pcs_entry_bounded M domain f count entry HD HF(proj1(HT entry)HE)) as(j&body&HJB&HB).
  destruct(pair_injective M entry j body k phi HJB HP) as[E E']. now subst j body.
Qed.

Lemma source_piece_table_valid_prefix M sb sc n:
  source_piece_table_valid M sb sc(succM M n) ->source_piece_table_valid M sb sc n.
Proof.
  intros HV entry count phi(i&HI&HE)HP. apply(HV entry count phi);[|exact HP].
  exists i. split;[exact(coding_lt_trans M i n(succM M n)HI(coding_lt_succ M n))|exact HE].
Qed.

Definition source_piece_conjunction_bound_at M n:=forall domain level sb sc d X out k,
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M d k ->coding_lt M X k ->
  source_piece_conjunction M domain level sb sc n d X out ->source_bounded M out k.
Definition source_piece_conjunction_bound_formula:form:=
  ∀∀∀∀∀∀∀∀(source_bounded_accept_formula $7(num 1) →source_bounded_accept_formula $6(num 2) →
    source_piece_table_valid_formula $5 $4 $8 →Peano.sless $3 $0 →Peano.sless $2 $0 →
    source_piece_conjunction_formula $7 $6 $5 $4 $8 $3 $2 $1 →source_bounded_accept_formula $1 $0).
Local Opaque source_piece_table_valid_formula Peano.sless source_piece_conjunction_formula.
Lemma source_piece_conjunction_bound_definable M:Definable1 M(source_piece_conjunction_bound_at M).
Proof.
  exists source_piece_conjunction_bound_formula,(fun _=>zeroM M). intro n.
  unfold source_piece_conjunction_bound_formula,source_piece_conjunction_bound_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_piece_table_valid_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite source_piece_conjunction_formula_correct.
  repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Theorem source_piece_conjunction_bounded M:forall n,source_piece_conjunction_bound_at M n.
Proof.
  apply(definable_induction M(source_piece_conjunction_bound_at M)(source_piece_conjunction_bound_definable M)).
  - intros domain level sb sc d X out k HD HL HV HDk HXk HOut.
    apply source_piece_conjunction_zero in HOut.
    apply(proj2(source_bounded_accept_binary M SFImpl(zeroM M)(zeroM M)out k
      (or_intror(or_intror eq_refl))HOut)). split;apply source_bounded_accept_falsity.
  - intros n IH domain level sb sc d X out k HD HL HV HDk HXk HOut.
    apply source_piece_conjunction_succ in HOut.
    destruct HOut as(previous&entry&count&phi&pc&HP&HE&HCount&HPC&HAnd).
    pose proof(IH domain level sb sc d X previous k HD HL(source_piece_table_valid_prefix M sb sc n HV)HDk HXk HP) as HPrevious.
    assert(HMember:context_member M sb sc(succM M n)entry) by(exists n;split;[apply coding_lt_succ|exact HE]).
    pose proof(source_pc_instance_bounded M domain level count phi d X pc k HD HL
      (HV entry count phi HMember HCount)HDk HXk HPC) as HPiece.
    exact(proj2(source_bounded_accept_binary M SFAnd previous pc out k(or_introl eq_refl)HAnd)
      (conj HPrevious HPiece)).
Qed.

Print Assumptions source_piece_table_valid_formula_correct.
Print Assumptions source_pcs_table_valid.
Print Assumptions source_piece_conjunction_bounded.

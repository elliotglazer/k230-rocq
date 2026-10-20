(** Actual source proofs introduce and project arbitrary internally finite
    PCf conjunctions. Both inductions use explicit PA formulas. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  Pairing SetFormulaCodes SourceBounded NumericalContexts NumericalEnvironments NumericalSourceFull
  SourcePieceClosure SourcePieceClosureFacts SourcePieceConjunction SourcePieceConjunctionFormula SourcePieceConjunctionBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_piece_proofs M domain level sb sc n d X b c l:=forall entry count phi pc,
  context_member M sb sc n entry ->pair_graph M count phi entry ->source_pc_instance M domain level count phi d X pc ->
  source_full_prv M b c l pc.
Definition source_piece_proofs_formula(domain level sb sc n d X b c l:term):form:=
  ∀∀∀∀(context_member_formula(pc_lift4 sb)(pc_lift4 sc)(pc_lift4 n)$3 →pair_formula $2 $1 $3 →
    source_pc_instance_formula(pc_lift4 domain)(pc_lift4 level)$2 $1(pc_lift4 d)(pc_lift4 X)$0 →
    source_full_prv_formula(pc_lift4 b)(pc_lift4 c)(pc_lift4 l)$0).
Local Opaque holds context_member_formula pair_formula source_pc_instance_formula source_full_prv_formula.
Theorem source_piece_proofs_formula_correct M rho domain level sb sc n d X b c l:
  holds M rho(source_piece_proofs_formula domain level sb sc n d X b c l) <->
  source_piece_proofs M(evalM M rho domain)(evalM M rho level)(evalM M rho sb)(evalM M rho sc)
    (evalM M rho n)(evalM M rho d)(evalM M rho X)(evalM M rho b)(evalM M rho c)(evalM M rho l).
Proof.
  unfold source_piece_proofs_formula,source_piece_proofs.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite pair_formula_correct.
  setoid_rewrite source_pc_instance_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  setoid_rewrite pc_eval_lift4. reflexivity.
Qed.

Lemma source_piece_proofs_prefix M domain level sb sc n d X b c l:
  source_piece_proofs M domain level sb sc(succM M n)d X b c l ->source_piece_proofs M domain level sb sc n d X b c l.
Proof.
  intros HH entry count phi pc(i&HI&HE)HP HPC. apply(HH entry count phi pc);try assumption.
  exists i. split;[exact(coding_lt_trans M i n(succM M n)HI(coding_lt_succ M n))|exact HE].
Qed.

Definition source_piece_conjunction_intro_at M n:=forall domain level sb sc d X out b c l k,
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M d k ->coding_lt M X k ->context_bounded M b c l k ->
  source_piece_conjunction M domain level sb sc n d X out ->source_piece_proofs M domain level sb sc n d X b c l ->
  source_full_prv M b c l out.
Definition source_piece_conjunction_intro_formula:form:=
  ∀∀∀∀∀∀∀∀∀∀∀(source_bounded_accept_formula $10(num 1) →source_bounded_accept_formula $9(num 2) →
    source_piece_table_valid_formula $8 $7 $11 →Peano.sless $6 $0 →Peano.sless $5 $0 →context_bounded_formula $3 $2 $1 $0 →
    source_piece_conjunction_formula $10 $9 $8 $7 $11 $6 $5 $4 →
    source_piece_proofs_formula $10 $9 $8 $7 $11 $6 $5 $3 $2 $1 →source_full_prv_formula $3 $2 $1 $4).
Local Opaque source_bounded_accept_formula source_piece_table_valid_formula Peano.sless context_bounded_formula
  source_piece_conjunction_formula source_piece_proofs_formula.
Lemma source_piece_conjunction_intro_definable M:Definable1 M(source_piece_conjunction_intro_at M).
Proof.
  exists source_piece_conjunction_intro_formula,(fun _=>zeroM M). intro n.
  unfold source_piece_conjunction_intro_formula,source_piece_conjunction_intro_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_piece_table_valid_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite source_piece_conjunction_formula_correct. setoid_rewrite source_piece_proofs_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Theorem source_piece_conjunction_intro M:forall n,source_piece_conjunction_intro_at M n.
Proof.
  apply(definable_induction M(source_piece_conjunction_intro_at M)(source_piece_conjunction_intro_definable M)).
  - intros domain level sb sc d X out b c l k HD HL HV HDk HXk HC HOut HH.
    apply source_piece_conjunction_zero in HOut.
    destruct(environment_cons_total M b c l(zeroM M)) as(ub&uc&un&HCons).
    assert(HNew:context_bounded M ub uc un k).
    { exact(proj2(context_bounded_cons M b c l(zeroM M)ub uc un k HCons)
        (conj(source_bounded_accept_falsity M k)HC)). }
    apply(full_source_II M b c l(zeroM M)(zeroM M)out ub uc un);[| |exact HCons|exact HOut].
    + exists k. split;[|exact HC].
      exact(proj2(source_bounded_accept_binary M SFImpl(zeroM M)(zeroM M)out k
        (or_intror(or_intror eq_refl))HOut)(conj(source_bounded_accept_falsity M k)(source_bounded_accept_falsity M k))).
    + apply full_source_Ctx;[exists k;auto using source_bounded_accept_falsity|].
      apply(proj2(context_member_cons M b c l(zeroM M)ub uc un(zeroM M)HCons)). now left.
  - intros n IH domain level sb sc d X out b c l k HD HL HV HDk HXk HC HOut HH.
    pose proof(source_piece_conjunction_bounded M(succM M n)domain level sb sc d X out k HD HL HV HDk HXk HOut) as HOutB.
    apply source_piece_conjunction_succ in HOut.
    destruct HOut as(previous&entry&count&phi&pc&HP&HE&HCount&HPC&HAnd).
    pose proof(IH domain level sb sc d X previous b c l k HD HL(source_piece_table_valid_prefix M sb sc n HV)
      HDk HXk HC HP(source_piece_proofs_prefix M domain level sb sc n d X b c l HH)) as PPrevious.
    apply(full_source_CI M b c l previous pc out(ex_intro _ k(conj HOutB HC))PPrevious);[|exact HAnd].
    apply(HH entry count phi pc);try assumption. exists n. split;[apply coding_lt_succ|exact HE].
Qed.

Definition source_piece_conjunction_project_at M n:=forall domain level sb sc d X out b c l k,
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M d k ->coding_lt M X k ->context_bounded M b c l k ->
  source_piece_conjunction M domain level sb sc n d X out ->source_full_prv M b c l out ->
  source_piece_proofs M domain level sb sc n d X b c l.
Definition source_piece_conjunction_project_formula:form:=
  ∀∀∀∀∀∀∀∀∀∀∀(source_bounded_accept_formula $10(num 1) →source_bounded_accept_formula $9(num 2) →
    source_piece_table_valid_formula $8 $7 $11 →Peano.sless $6 $0 →Peano.sless $5 $0 →context_bounded_formula $3 $2 $1 $0 →
    source_piece_conjunction_formula $10 $9 $8 $7 $11 $6 $5 $4 →source_full_prv_formula $3 $2 $1 $4 →
    source_piece_proofs_formula $10 $9 $8 $7 $11 $6 $5 $3 $2 $1).
Lemma source_piece_conjunction_project_definable M:Definable1 M(source_piece_conjunction_project_at M).
Proof.
  exists source_piece_conjunction_project_formula,(fun _=>zeroM M). intro n.
  unfold source_piece_conjunction_project_formula,source_piece_conjunction_project_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_piece_table_valid_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite source_piece_conjunction_formula_correct. setoid_rewrite source_piece_proofs_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Theorem source_piece_conjunction_project M:forall n,source_piece_conjunction_project_at M n.
Proof.
  apply(definable_induction M(source_piece_conjunction_project_at M)(source_piece_conjunction_project_definable M)).
  - intros domain level sb sc d X out b c l k HD HL HV HDk HXk HC HOut POut entry count phi pc HE HP HPC.
    exfalso. exact(context_empty M sb sc entry HE).
  - intros n IH domain level sb sc d X out b c l k HD HL HV HDk HXk HC HOut POut entry count phi pc(i&HI&HE)HP HPC.
    apply source_piece_conjunction_succ in HOut.
    destruct HOut as(previous&last&lastCount&lastPhi&lastPc&HPrevious&HLast&HLastPair&HLastPc&HAnd).
    pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
    destruct(proj1(coding_lt_succ_cases M i n)HI) as[HI'|E].
    + assert(PPrevious:source_full_prv M b c l previous).
      { apply(full_source_CE1 M b c l previous lastPc out);[|exact POut|exact HAnd].
        exists k. split;[|exact HC]. exact(source_piece_conjunction_bounded M n domain level sb sc d X previous k
          HD HL HPrefix HDk HXk HPrevious). }
      exact(IH domain level sb sc d X previous b c l k HD HL HPrefix HDk HXk HC HPrevious PPrevious
        entry count phi pc(ex_intro _ i(conj HI' HE))HP HPC).
    + subst i. pose proof(beta_unique M sb sc n entry last HE HLast) as E. subst last.
      destruct(pair_injective M entry count phi lastCount lastPhi HP HLastPair) as[E E']. subst lastCount lastPhi.
      pose proof(source_pc_instance_functional M domain level count phi d X lastPc pc HLastPc HPC) as E. subst lastPc.
      apply(full_source_CE2 M b c l previous pc out);[|exact POut|exact HAnd].
      exists k. split;[|exact HC].
      apply(source_pc_instance_bounded M domain level count phi d X pc k HD HL);try assumption.
      apply(HV entry count phi);[exists n;split;[apply coding_lt_succ|exact HE]|exact HP].
Qed.

Print Assumptions source_piece_proofs_formula_correct.
Print Assumptions source_piece_conjunction_intro.
Print Assumptions source_piece_conjunction_project.

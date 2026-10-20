(** First-order witness-closure inputs for the uniform TV induction.
    The carrier is a source variable, and renaming is actual coded syntax. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
  SourcePieceWitnessUnary NumericalInstantiation SourceDomainInstances SourceUnaryRenamingGraph
  NumericalRenamingMaps NumericalRenaming SourceDomainInstanceRenaming.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.
Definition source_piece_witness_instance M domain count piece carrier out:=exists unary,
  source_piece_witness_unary M domain count piece unary /\numerical_instantiation M unary carrier out.
Definition source_piece_witness_instance_formula(domain count piece carrier out:term):form:=∃(
  source_piece_witness_unary_formula domain`[↑] count`[↑] piece`[↑] $0 ∧
  numerical_instantiation_formula $0 carrier`[↑] out`[↑]).
Local Opaque holds source_piece_witness_unary_formula numerical_instantiation_formula.
Theorem source_piece_witness_instance_formula_correct M rho domain count piece carrier out:
  holds M rho(source_piece_witness_instance_formula domain count piece carrier out) <->
  source_piece_witness_instance M(evalM M rho domain)(evalM M rho count)(evalM M rho piece)
    (evalM M rho carrier)(evalM M rho out).
Proof.
  unfold source_piece_witness_instance_formula,source_piece_witness_instance.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_piece_witness_unary_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct. unfold evalM.
  repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_piece_witness_instance_total M domain count piece carrier:
  exists out,source_piece_witness_instance M domain count piece carrier out.
Proof.
  destruct(source_piece_witness_unary_total M domain count piece)as(unary&HU).
  destruct(numerical_instantiation_total M unary carrier)as(out&HO). exists out,unary. auto.
Qed.
Theorem source_piece_witness_instance_functional M domain count piece carrier x y:
  source_piece_witness_instance M domain count piece carrier x ->
  source_piece_witness_instance M domain count piece carrier y ->x=y.
Proof.
  intros(u&HU&HX)(v&HV&HY).
  pose proof(source_piece_witness_unary_functional M domain count piece u v HU HV)as E. subst v.
  exact(numerical_instantiation_functional M u carrier x y HX HY).
Qed.
Theorem source_piece_witness_instance_bounded M domain count piece carrier out k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  coding_lt M carrier k ->source_piece_witness_instance M domain count piece carrier out ->source_bounded M out k.
Proof.
  intros HD HP HC(unary&HU&HO).
  exact(source_domain_instance_bound M unary carrier out k
    (source_piece_witness_unary_bounded M domain count piece unary HD HP HU)HC HO).
Qed.
Theorem source_piece_witness_instance_renaming M domain count piece carrier out rb rc rn delta carrier' out':
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  source_piece_witness_instance M domain count piece carrier out ->
  renaming_lookup M rb rc rn delta carrier carrier' ->numerical_renaming M out rb rc rn delta out' ->
  source_piece_witness_instance M domain count piece carrier' out'.
Proof.
  intros HD HP(unary&HU&HO)HC HR. exists unary. split;[exact HU|].
  exact(source_domain_instance_renaming M unary carrier out rb rc rn delta out' carrier'
    (source_piece_witness_unary_bounded M domain count piece unary HD HP HU)HO HR HC).
Qed.
Theorem source_piece_witness_instance_renaming_graph M domain count piece carrier out rb rc rn delta carrier' out':
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  source_piece_witness_instance M domain count piece carrier out ->
  renaming_lookup M rb rc rn delta carrier carrier' ->
  source_piece_witness_instance M domain count piece carrier' out' ->numerical_renaming M out rb rc rn delta out'.
Proof.
  intros HD HP(unary&HU&HO)HC(unary'&HU'&HO').
  pose proof(source_piece_witness_unary_functional M domain count piece unary' unary HU' HU)as E. subst unary'.
  exact(source_unary_instance_renaming_graph M unary carrier out rb rc rn delta carrier' out'
    (source_piece_witness_unary_bounded M domain count piece unary HD HP HU)HO HC HO').
Qed.
Print Assumptions source_piece_witness_instance_formula_correct.
Print Assumptions source_piece_witness_instance_total.
Print Assumptions source_piece_witness_instance_functional.
Print Assumptions source_piece_witness_instance_bounded.
Print Assumptions source_piece_witness_instance_renaming.
Print Assumptions source_piece_witness_instance_renaming_graph.

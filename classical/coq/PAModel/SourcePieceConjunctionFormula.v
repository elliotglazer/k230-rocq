(** An explicit arithmetic formula for the internally finite PCf graph. *)
From PAModel Require Import Model FiniteCoding NumericalProofs CodeExpressions InternalRecursion SourcePieceConjunction.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition piece_lift6(t:term):=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma piece_eval_lift6 M rho a b c d e f t:
  evalM M(a.:b.:c.:d.:e.:f.:rho)(piece_lift6 t)=evalM M rho t.
Proof. unfold piece_lift6,evalM. now rewrite !eval_up. Qed.

Definition source_piece_conjunction_formula(domain level sb sc n d X result:term):form:=
  ∃∃∃∃∃∃(($0==piece_lift6 domain) ∧(($1==piece_lift6 level) ∧
    (($2==piece_lift6 sb) ∧(($3==piece_lift6 sc) ∧(($4==piece_lift6 d) ∧
    (($5==piece_lift6 X) ∧recursion_graph_formula source_piece_conjunction_step_formula
      (piece_lift6 n)(piece_lift6 result))))))).
Lemma piece_holds_equal M rho t u:holds M rho(t==u) <->evalM M rho t=evalM M rho u.
Proof. reflexivity. Qed.
Local Opaque holds recursion_graph_formula.

Theorem source_piece_conjunction_formula_correct M rho domain level sb sc n d X result:
  holds M rho(source_piece_conjunction_formula domain level sb sc n d X result) <->
  source_piece_conjunction M(evalM M rho domain)(evalM M rho level)(evalM M rho sb)(evalM M rho sc)
    (evalM M rho n)(evalM M rho d)(evalM M rho X)(evalM M rho result).
Proof.
  unfold source_piece_conjunction_formula. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite recursion_graph_formula_correct. setoid_rewrite source_piece_conjunction_recursion.
  setoid_rewrite piece_holds_equal. setoid_rewrite piece_eval_lift6.
  change ((exists a b c d' e f,
    f=evalM M rho domain /\e=evalM M rho level /\d'=evalM M rho sb /\c=evalM M rho sc /\
    b=evalM M rho d /\a=evalM M rho X /\
    source_piece_conjunction M f e d' c(evalM M rho n)b a(evalM M rho result)) <->
    source_piece_conjunction M(evalM M rho domain)(evalM M rho level)(evalM M rho sb)(evalM M rho sc)
      (evalM M rho n)(evalM M rho d)(evalM M rho X)(evalM M rho result)).
  split.
  - intros(a&b&c&d'&e&f&->&->&->&->&->&->&H). exact H.
  - intro H. exists(evalM M rho X),(evalM M rho d),(evalM M rho sc),(evalM M rho sb),
      (evalM M rho level),(evalM M rho domain). auto 10.
Qed.

Print Assumptions source_piece_conjunction_formula_correct.

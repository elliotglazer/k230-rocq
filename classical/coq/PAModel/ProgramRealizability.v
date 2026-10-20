(** First-order continuation blocks used by the internal proof compiler. *)
From PAModel Require Import Model FiniteCoding NumericalProofs SearchStep RunSyntax
  NumericalReachability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition program_block M f tail p : Prop :=
  forall np t w,
    numerical_halts_from M (mkSearchState (carrier M) p np t w (zeroM M) (zeroM M)) \/
    numerical_reaches M (mkSearchState (carrier M) p np t w (zeroM M) (zeroM M))
      (mkSearchState (carrier M) tail np f w (zeroM M) (zeroM M)).
Definition program_realizes M f : Prop := forall tail, exists p, program_block M f tail p.

Definition program_realizes_formula (f : term) : form :=
  ∀∃∀∀∀
    (halts_from_formula (mkSearchState term $3 $2 $1 $0 zero zero) ∨
      reach_formula (mkSearchState term $3 $2 $1 $0 zero zero)
        (mkSearchState term $4 $2 (run_lift 5 f) $0 zero zero)).

Lemma eval_run_lift5 M rho a b c d e t :
  evalM M (e .: d .: c .: b .: a .: rho) (run_lift 5 t)=evalM M rho t.
Proof. unfold evalM;cbn [run_lift]. now rewrite !eval_up. Qed.

Local Opaque holds halts_from_formula reach_formula.
Theorem program_realizes_formula_correct M rho f :
  holds M rho (program_realizes_formula f) <-> program_realizes M (evalM M rho f).
Proof.
  unfold program_realizes_formula,program_realizes,program_block.
  rewrite holds_all. setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_or.
  setoid_rewrite halts_from_formula_correct. setoid_rewrite reach_formula_correct.
  unfold term_state_value. cbn -[evalM run_lift].
  setoid_rewrite eval_run_lift5. reflexivity.
Qed.

Theorem program_realizes_definable M : Definable1 M(program_realizes M).
Proof.
  exists(program_realizes_formula $0),(fun _=>zeroM M).
  intro f. symmetry. exact(program_realizes_formula_correct M _ $0).
Qed.

Print Assumptions program_realizes_formula_correct.
Print Assumptions program_realizes_definable.

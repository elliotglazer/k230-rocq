(** A singleton whose two bound role names are fixed by a caller-chosen
    allocation base. Diagonal pairing supplies the actual existence proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps TemplatePropositional ProofMacros QuantifierMacros
  NumericalKP0 NumericalBootstrap NumericalSingleton NumericalRawPair
  NumericalTaggedComprehension QuotientAtomTemplates ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma diagonal_pair_singleton_program X P Z :
  proof_macro nil nil (E_wim (E_raw_pair X X P Z) (E_raw_singleton X P Z)).
Proof.
  assert (HProfile:proof_macro nil nil
    (E_wim (E_wal Z (E_wim (E_wel Z P) (E_or (E_weq Z X) (E_weq Z X))))
      (E_wal Z (E_wim (E_wel Z P) (E_weq Z X))))).
  { apply macro_all_monotone,kp0_implication_map.
    apply tagged_or_cases;apply PM_template,template_I. }
  unfold E_raw_pair,E_raw_singleton. apply macro_discharge,macro_deduction,kp0_md_conjunction.
  - apply tagged_md_left with (b:=E_wel X P).
    apply tagged_md_left with
      (b:=E_wal Z (E_wim (E_wel Z P) (E_or (E_weq Z X) (E_weq Z X)))),
      md_hyp;now left.
  - eapply md_mp;[|apply md_global;exact HProfile].
    apply tagged_md_right with (a:=E_wa (E_wel X P) (E_wel X P)),md_hyp;now left.
Qed.

Theorem numerical_chosen_singleton M rho X fresh x base :
  code_relation M rho X x -> code_relation M rho fresh base ->
  coding_lt M (zeroM M) base -> coding_lt M x base ->
  ns_proof M rho
    (E_wex (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
      (E_raw_singleton X (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
        (CEadd (CEadd (CEadd fresh (CEconst 1)) (CEconst 1)) (CEconst 1)))).
Proof.
  intros HX HF H0 Hx.
  apply (ns_proof_mp M rho
    (E_wex (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
      (E_raw_pair X X (CEadd (CEadd fresh (CEconst 1)) (CEconst 1))
        (CEadd (CEadd (CEadd fresh (CEconst 1)) (CEconst 1)) (CEconst 1))))).
  - exact (numerical_raw_pair_named M rho X X fresh x x base HX HX HF H0 Hx Hx).
  - apply ns_proof_macro with (inputs:=nil);[intros e []|].
    apply macro_exists_monotone,diagonal_pair_singleton_program.
Qed.

Print Assumptions diagonal_pair_singleton_program.
Print Assumptions numerical_chosen_singleton.

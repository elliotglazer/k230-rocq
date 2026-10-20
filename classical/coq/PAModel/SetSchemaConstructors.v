(** Finite constructors for the two conventional ZFC axiom schemas.
    The supplied body codes are already renamed into the indicated scope.
    No numerical lifting, substitution, or schema-recognition graph is
    assumed to exist in this module. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds StandardModel SetFormulaCodes.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition sep_substitution : nat -> sf_term :=
  $0 .: (Nat.add 3 >> var).
Definition rep_substitution_A : nat -> sf_term :=
  $2 .: $1 .: (Nat.add 3 >> var).
Definition rep_substitution_B : nat -> sf_term :=
  $2 .: $0 .: (Nat.add 3 >> var).
Definition rep_substitution_C : nat -> sf_term :=
  $0 .: $1 .: (Nat.add 4 >> var).

Definition source_sep_body (phi : sf_form) := phi[sep_substitution].
Definition source_rep_body_A (phi : sf_form) := phi[rep_substitution_A].
Definition source_rep_body_B (phi : sf_form) := phi[rep_substitution_B].
Definition source_rep_body_C (phi : sf_form) := phi[rep_substitution_C].

(** Pointwise descriptions of the exact source renamings. A and B are not
    pure lifts: the former moves free variable 0, the latter moves 0 and 1. *)
Lemma sep_substitution_index i :
  sf_index (sep_substitution i) = match i with 0 => 0 | S k => k+3 end.
Proof. destruct i; cbn; lia. Qed.
Lemma rep_substitution_A_index i :
  sf_index (rep_substitution_A i) =
    match i with 0 => 2 | 1 => 1 | S (S k) => k+3 end.
Proof. destruct i as [|[|i]]; cbn; lia. Qed.
Lemma rep_substitution_B_index i :
  sf_index (rep_substitution_B i) =
    match i with 0 => 2 | 1 => 0 | S (S k) => k+3 end.
Proof. destruct i as [|[|i]]; cbn; lia. Qed.
Lemma rep_substitution_C_index i :
  sf_index (rep_substitution_C i) =
    match i with 0 => 0 | 1 => 1 | S (S k) => k+4 end.
Proof. destruct i as [|[|i]]; cbn; lia. Qed.

(** This is the exact binder rule needed by a numerical renaming trace.
    It is a theorem about source substitutions, not an internal recursion. *)
Lemma source_up_substitution_index (sigma : nat -> sf_term) i :
  sf_index (up sigma i) =
  match i with 0 => 0 | S k => S (sf_index (sigma k)) end.
Proof.
  destruct i as [|i]; [reflexivity|].
  cbn. unfold funcomp. destruct (sigma i) as [j|[]]. reflexivity.
Qed.

Definition E_sf_iff (a b : code_expr) :=
  E_sf SFAnd (E_sf SFImpl a b) (E_sf SFImpl b a).
Definition E_sf_mem (i j : nat) := E_sf SFMember (CEconst i) (CEconst j).
Definition E_sf_eq (i j : nat) := E_sf SFEqual (CEconst i) (CEconst j).
Definition E_sf_all (a : code_expr) := E_sf SFAll a (CEconst 0).
Definition E_sf_ex (a : code_expr) := E_sf SFEx a (CEconst 0).

(** body is phi[0 .: (k |-> k+3)], inside all/ex/all. *)
Definition E_sf_separation (body : code_expr) :=
  E_sf_all (E_sf_ex (E_sf_all
    (E_sf_iff (E_sf_mem 0 1) (E_sf SFAnd (E_sf_mem 0 2) body)))).

(** Both bodies are inside all/all/all. *)
Definition E_sf_functionality (bodyA bodyB : code_expr) :=
  E_sf_all (E_sf_all (E_sf_all
    (E_sf SFImpl bodyA (E_sf SFImpl bodyB (E_sf_eq 1 0))))).

(** bodyC is inside all/ex/all/ex. *)
Definition E_sf_replacement (bodyA bodyB bodyC : code_expr) :=
  E_sf SFImpl (E_sf_functionality bodyA bodyB)
    (E_sf_all (E_sf_ex (E_sf_all
      (E_sf_iff (E_sf_mem 0 1)
        (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3) bodyC)))))).

Definition schema_env3 {A} (a b c : A) i :=
  match i with 0 => a | 1 => b | _ => c end.

Local Opaque KCode230.P.

Theorem sf_separation_source_calibration phi :
  sf_encode (ax_sep' phi) =
  code_value (fun _ => sf_encode (source_sep_body phi))
    (E_sf_separation (CEvar 0)).
Proof.
  unfold ax_sep',source_sep_body,E_sf_separation,E_sf_iff,
    E_sf_mem,E_sf_all,E_sf_ex.
  repeat rewrite sf_make_value. reflexivity.
Qed.

Theorem sf_functionality_source_calibration phi :
  sf_encode (fun_rel' phi) =
  code_value (schema_env3 (sf_encode (source_rep_body_A phi))
    (sf_encode (source_rep_body_B phi)) 0)
    (E_sf_functionality (CEvar 0) (CEvar 1)).
Proof.
  unfold fun_rel',source_rep_body_A,source_rep_body_B,
    E_sf_functionality,E_sf_eq,E_sf_all.
  repeat rewrite sf_make_value. reflexivity.
Qed.

Theorem sf_replacement_source_calibration phi :
  sf_encode (ax_rep' phi) =
  code_value (schema_env3 (sf_encode (source_rep_body_A phi))
    (sf_encode (source_rep_body_B phi)) (sf_encode (source_rep_body_C phi)))
    (E_sf_replacement (CEvar 0) (CEvar 1) (CEvar 2)).
Proof.
  unfold ax_rep',fun_rel',source_rep_body_A,source_rep_body_B,source_rep_body_C,
    E_sf_replacement,E_sf_functionality,E_sf_iff,E_sf_mem,E_sf_eq,E_sf_all,E_sf_ex.
  repeat rewrite sf_make_value. reflexivity.
Qed.

Definition sf_separation_constructor M body z :=
  code_relation M (fun _ => body) (E_sf_separation (CEvar 0)) z.
Definition sf_replacement_constructor M bodyA bodyB bodyC z :=
  code_relation M (schema_env3 bodyA bodyB bodyC)
    (E_sf_replacement (CEvar 0) (CEvar 1) (CEvar 2)) z.

Definition sf_separation_constructor_formula (body z : pa_term) : pa_form :=
  code_formula (E_sf_separation (CEvar 0)) (fun _ => body) z.
Definition sf_replacement_constructor_formula (bodyA bodyB bodyC z : pa_term) : pa_form :=
  code_formula (E_sf_replacement (CEvar 0) (CEvar 1) (CEvar 2))
    (schema_env3 bodyA bodyB bodyC) z.

Theorem sf_separation_constructor_correct M rho body z :
  holds M rho (sf_separation_constructor_formula body z) <->
  sf_separation_constructor M (evalM M rho body) (evalM M rho z).
Proof. apply code_formula_correct. Qed.

Theorem sf_replacement_constructor_correct M rho a b c z :
  holds M rho (sf_replacement_constructor_formula a b c z) <->
  sf_replacement_constructor M (evalM M rho a) (evalM M rho b)
    (evalM M rho c) (evalM M rho z).
Proof.
  unfold sf_replacement_constructor_formula,sf_replacement_constructor.
  rewrite code_formula_correct. apply code_relation_ext.
  intros [|[|i]]; reflexivity.
Qed.

Lemma sf_separation_constructor_total M body :
  exists z, sf_separation_constructor M body z.
Proof. apply code_relation_total. Qed.

Lemma sf_replacement_constructor_total M a b c :
  exists z, sf_replacement_constructor M a b c z.
Proof. apply code_relation_total. Qed.

Lemma sf_separation_constructor_functional M body z z' :
  sf_separation_constructor M body z -> sf_separation_constructor M body z' -> z=z'.
Proof. apply code_relation_functional. Qed.

Lemma sf_replacement_constructor_functional M a b c z z' :
  sf_replacement_constructor M a b c z -> sf_replacement_constructor M a b c z' -> z=z'.
Proof. apply code_relation_functional. Qed.

Theorem sf_separation_constructor_standard phi z :
  sf_separation_constructor natModel (sf_encode (source_sep_body phi)) z <->
    z = sf_encode (ax_sep' phi).
Proof.
  unfold sf_separation_constructor. rewrite code_relation_natModel.
  rewrite sf_separation_source_calibration. reflexivity.
Qed.

Theorem sf_replacement_constructor_standard phi z :
  sf_replacement_constructor natModel
    (sf_encode (source_rep_body_A phi)) (sf_encode (source_rep_body_B phi))
    (sf_encode (source_rep_body_C phi)) z <-> z = sf_encode (ax_rep' phi).
Proof.
  unfold sf_replacement_constructor. rewrite code_relation_natModel.
  rewrite sf_replacement_source_calibration. reflexivity.
Qed.

Lemma sf_separation_constructor_bounded :
  bounded 2 (sf_separation_constructor_formula $1 $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Lemma sf_replacement_constructor_bounded :
  bounded 4 (sf_replacement_constructor_formula $3 $2 $1 $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions sf_separation_source_calibration.
Print Assumptions sf_functionality_source_calibration.
Print Assumptions sf_replacement_source_calibration.
Print Assumptions sf_separation_constructor_correct.
Print Assumptions sf_replacement_constructor_correct.
Print Assumptions sf_separation_constructor_total.
Print Assumptions sf_replacement_constructor_total.
Print Assumptions sf_separation_constructor_functional.
Print Assumptions sf_replacement_constructor_functional.
Print Assumptions sf_separation_constructor_standard.
Print Assumptions sf_replacement_constructor_standard.
Print Assumptions sf_separation_constructor_bounded.
Print Assumptions sf_replacement_constructor_bounded.
Print Assumptions source_up_substitution_index.

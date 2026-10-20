(** A numerical interface for the full de Bruijn set-formula syntax.

    This is a separate code from the machine's named-variable Hilbert code.
    It has genuine falsity and primitive conjunction, disjunction, implication
    and both quantifiers.  It is not yet a proof checker or an internal
    translation of arbitrary coded formulas.  The graphs below apply to
    arbitrary, possibly nonstandard, arithmetic arguments. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Arith.PeanoNat.
Import Vector.VectorNotations.
Unset Implicit Arguments.

Definition sf_term := @Core.term sig_empty.
Definition sf_form := @Core.form sig_empty ZFSignature.ZF_pred_sig
  full_operators falsity_on.
Definition pa_term := @Core.term PA_funcs_signature.
Definition pa_form := @Core.form PA_funcs_signature PA_preds_signature
  full_operators falsity_on.

(** Tags 1..7 distinguish the non-falsity constructors.  Unary constructors
    use a zero second payload.  A quantifier stores no variable label. *)
Inductive sf_head := SFMember | SFEqual | SFAnd | SFOr | SFImpl | SFAll | SFEx.
Definition sf_tag (h : sf_head) : nat :=
  match h with
  | SFMember => 1 | SFEqual => 2 | SFAnd => 3 | SFOr => 4
  | SFImpl => 5 | SFAll => 6 | SFEx => 7
  end.

Definition E_sf_pair (tag : nat) (a b : code_expr) : code_expr :=
  CEadd (CEmul (CEconst 8) (CEpair a b)) (CEconst tag).
Definition E_sf (h : sf_head) (a b : code_expr) : code_expr :=
  match h with
  | SFAll | SFEx => E_sf_pair (sf_tag h) a (CEconst 0)
  | _ => E_sf_pair (sf_tag h) a b
  end.

Definition sf_env {A : Type} (a b : A) (i : nat) : A :=
  match i with 0 => a | _ => b end.
Definition sf_relation (M : Model) (h : sf_head)
    (a b z : carrier M) : Prop :=
  code_relation M (sf_env a b) (E_sf h (CEvar 0) (CEvar 1)) z.
Definition sf_formula (h : sf_head) (a b z : pa_term) : pa_form :=
  code_formula (E_sf h (CEvar 0) (CEvar 1)) (sf_env a b) z.

Lemma sf_formula_correct (M : Model) rho h a b z :
  holds M rho (sf_formula h a b z) <->
  sf_relation M h (evalM M rho a) (evalM M rho b) (evalM M rho z).
Proof.
  unfold sf_formula, sf_relation. rewrite code_formula_correct.
  apply code_relation_ext. intros [|i]; reflexivity.
Qed.

Lemma sf_relation_total (M : Model) h a b :
  exists z, sf_relation M h a b z.
Proof. apply code_relation_total. Qed.

Lemma sf_relation_functional (M : Model) h a b z z' :
  sf_relation M h a b z -> sf_relation M h a b z' -> z = z'.
Proof. apply code_relation_functional. Qed.

Definition sf_index (t : sf_term) : nat :=
  match t with var i => i | func f _ => False_rect _ f end.

Definition sf_make (h : sf_head) (a b : nat) : nat :=
  code_value (sf_env a b) (E_sf h (CEvar 0) (CEvar 1)).

Fixpoint sf_encode {ff} (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) : nat :=
  match phi with
  | falsity => 0
  | atom P v =>
      match P return Vector.t sf_term (ZF_pred_ar P) -> nat with
      | elem => fun v => sf_make SFMember (sf_index (Vector.hd v))
          (sf_index (Vector.hd (Vector.tl v)))
      | equal => fun v => sf_make SFEqual (sf_index (Vector.hd v))
          (sf_index (Vector.hd (Vector.tl v)))
      end v
  | bin op a b =>
      sf_make (match op with Conj => SFAnd | Disj => SFOr | Impl => SFImpl end)
        (sf_encode a) (sf_encode b)
  | quant q a =>
      sf_make (match q with All => SFAll | Ex => SFEx end) (sf_encode a) 0
  end.

Lemma sf_make_value env h a b :
  code_value env (E_sf h a b) =
  sf_make h (code_value env a) (code_value env b).
Proof. destruct h; reflexivity. Qed.

(** Both guards are already in the scope of the new binder.  In particular,
    [g] is NOT silently shifted here.  The quotient guard below adds the one
    required shift to the domain variable and compares it with variable 0. *)
Definition E_sf_guard_all (g a : code_expr) :=
  E_sf SFAll (E_sf SFImpl g a) (CEconst 0).
Definition E_sf_guard_ex (g a : code_expr) :=
  E_sf SFEx (E_sf SFAnd g a) (CEconst 0).
Definition E_sf_qguard (t : code_expr) :=
  E_sf SFMember (CEadd t (CEconst 1)) (CEconst 0).
Definition E_sf_qall (t a : code_expr) := E_sf_guard_all (E_sf_qguard t) a.
Definition E_sf_qex (t a : code_expr) := E_sf_guard_ex (E_sf_qguard t) a.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Definition sf_guarded_all (g a : sf_form) : sf_form :=
  quant All (bin Impl g a).
Definition sf_guarded_ex (g a : sf_form) : sf_form :=
  quant Ex (bin Conj g a).
Definition sf_qguard (i : nat) : sf_form :=
  atom elem ([var (S i); var 0]).

Lemma sf_guard_all_code env g a :
  code_value env (E_sf_guard_all g a) =
  sf_make SFAll (sf_make SFImpl (code_value env g) (code_value env a)) 0.
Proof. unfold E_sf_guard_all. now rewrite !sf_make_value. Qed.

Lemma sf_guard_ex_code env g a :
  code_value env (E_sf_guard_ex g a) =
  sf_make SFEx (sf_make SFAnd (code_value env g) (code_value env a)) 0.
Proof. unfold E_sf_guard_ex. now rewrite !sf_make_value. Qed.

Lemma sf_guard_all_calibrated g a :
  sf_encode (sf_guarded_all g a) =
  code_value (sf_env (sf_encode g) (sf_encode a))
    (E_sf_guard_all (CEvar 0) (CEvar 1)).
Proof. rewrite sf_guard_all_code. reflexivity. Qed.

Lemma sf_guard_ex_calibrated g a :
  sf_encode (sf_guarded_ex g a) =
  code_value (sf_env (sf_encode g) (sf_encode a))
    (E_sf_guard_ex (CEvar 0) (CEvar 1)).
Proof. rewrite sf_guard_ex_code. reflexivity. Qed.

Lemma sf_qall_calibrated i a :
  sf_encode (sf_guarded_all (sf_qguard i) a) =
  code_value (sf_env i (sf_encode a)) (E_sf_qall (CEvar 0) (CEvar 1)).
Proof.
  unfold E_sf_qall, E_sf_qguard. rewrite sf_guard_all_code, sf_make_value.
  cbn [code_value sf_env sf_encode sf_guarded_all sf_qguard sf_index].
  now rewrite Nat.add_1_r.
Qed.

Lemma sf_qex_calibrated i a :
  sf_encode (sf_guarded_ex (sf_qguard i) a) =
  code_value (sf_env i (sf_encode a)) (E_sf_qex (CEvar 0) (CEvar 1)).
Proof.
  unfold E_sf_qex, E_sf_qguard. rewrite sf_guard_ex_code, sf_make_value.
  cbn [code_value sf_env sf_encode sf_guarded_ex sf_qguard sf_index].
  now rewrite Nat.add_1_r.
Qed.

Definition sf_qexpression (universal : bool) : code_expr :=
  if universal then E_sf_qall (CEvar 0) (CEvar 1)
  else E_sf_qex (CEvar 0) (CEvar 1).
Definition sf_qrelation (M : Model) (universal : bool)
    (t a z : carrier M) : Prop :=
  code_relation M (sf_env t a) (sf_qexpression universal) z.
Definition sf_qformula (universal : bool) (t a z : pa_term) : pa_form :=
  code_formula (sf_qexpression universal) (sf_env t a) z.

Theorem sf_qformula_correct (M : Model) rho universal t a z :
  holds M rho (sf_qformula universal t a z) <->
  sf_qrelation M universal (evalM M rho t) (evalM M rho a) (evalM M rho z).
Proof.
  unfold sf_qformula, sf_qrelation. rewrite code_formula_correct.
  apply code_relation_ext. intros [|i]; reflexivity.
Qed.

Theorem sf_qrelation_total (M : Model) universal t a :
  exists z, sf_qrelation M universal t a z.
Proof. apply code_relation_total. Qed.

Theorem sf_qrelation_functional (M : Model) universal t a z z' :
  sf_qrelation M universal t a z -> sf_qrelation M universal t a z' -> z = z'.
Proof. apply code_relation_functional. Qed.

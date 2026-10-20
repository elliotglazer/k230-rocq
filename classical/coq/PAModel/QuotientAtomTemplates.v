(** Finite source formulas for the tagged bisimulation quotient, and their
    named-code templates. The definitions below reproduce Sing0/Pair0/OP0/App0
    in the pinned Z_base.v and dchild/dbisim/deqv/dmem in KQuot.v.
    Porting their derivations and checking the reference-module identities
    remain separate from this numerical syntax construction. *)
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From PAModel Require Import CodeExpressions NumericalFold.
Import Vector.VectorNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition set_term := @Core.term sig_empty.
Definition set_form := @Core.form sig_empty ZF_pred_sig full_operators falsity_on.

Definition source_Sing0 (x s : set_term) : set_form :=
  x ∈' s ∧ ∀ ($0 ∈' s`[↑] → $0 ≡' x`[↑]).
Definition source_Pair0 (x y p : set_term) : set_form :=
  x ∈' p ∧ y ∈' p ∧ ∀ ($0 ∈' p`[↑] → $0 ≡' x`[↑] ∨ $0 ≡' y`[↑]).
Definition source_OP0 (x y p : set_term) : set_form :=
  (∃ ($0 ∈' p`[↑] ∧ source_Sing0 x`[↑] $0)) ∧
  (∃ ($0 ∈' p`[↑] ∧ source_Pair0 x`[↑] y`[↑] $0)) ∧
  ∀ ($0 ∈' p`[↑] → source_Sing0 x`[↑] $0 ∨ source_Pair0 x`[↑] y`[↑] $0).
Definition source_App0 (f u v : set_term) : set_form :=
  ∃ ($0 ∈' f`[↑] ∧ source_OP0 u`[↑] v`[↑] $0).
Definition source_dchild (t x y : set_term) : set_form := t ∈' x ∧ x ∈' y.
Definition source_dbisim (t r : set_term) : set_form :=
  t ∈' r ∧ ∀ ∀ (source_App0 r`[↑]`[↑] $1 $0 →
    (t`[↑]`[↑] ∈' $1 ∧ t`[↑]`[↑] ∈' $0) ∧
    ((∀ (source_dchild t`[↑]`[↑]`[↑] $0 $2 →
         ∃ (source_dchild t`[↑]`[↑]`[↑]`[↑] $0 $2 ∧
           source_App0 r`[↑]`[↑]`[↑]`[↑] $1 $0))) ∧
     (∀ (source_dchild t`[↑]`[↑]`[↑] $0 $1 →
         ∃ (source_dchild t`[↑]`[↑]`[↑]`[↑] $0 $3 ∧
           source_App0 r`[↑]`[↑]`[↑]`[↑] $0 $1))))).
Definition source_deqv (t x y : set_term) : set_form :=
  ∃ (source_dbisim t`[↑] $0 ∧ source_App0 $0 x`[↑] y`[↑]).
Definition source_dmem (t x y : set_term) : set_form :=
  ∃ (source_dchild t`[↑] $0 y`[↑] ∧ source_deqv t`[↑] x`[↑] $0).

Definition E_or a b := E_wim (E_wn a) b.

Definition template_term (env : nat -> code_expr) (t : set_term) : code_expr :=
  match t with
  | var i => env i
  | func f _ => match f with end
  end.

(** Each new binder receives the current fresh name. Descending under that
    binder increments it. Disjoint branches can safely reuse bound names. *)
Fixpoint template_set_formula {ff} (env : nat -> code_expr) (fresh : code_expr)
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : code_expr :=
  match phi with
  | falsity => CEconst 1
  | atom P v =>
      match P return Vector.t set_term (ar_preds P) -> code_expr with
      | elem => fun v => E_wel (template_term env (Vector.hd v))
          (template_term env (Vector.hd (Vector.tl v)))
      | equal => fun v => E_weq (template_term env (Vector.hd v))
          (template_term env (Vector.hd (Vector.tl v)))
      end v
  | bin Conj a b => E_wa (template_set_formula env fresh a) (template_set_formula env fresh b)
  | bin Disj a b => E_or (template_set_formula env fresh a) (template_set_formula env fresh b)
  | bin Impl a b => E_wim (template_set_formula env fresh a) (template_set_formula env fresh b)
  | quant All a => E_wal fresh (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)
  | quant Ex a => E_wex fresh (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)
  end.

(** In the fold environment: slots 0,1 are the two source variables;
    slot 2 is the fixed quotient tag; slot 3 is the fixed fresh-name base. *)
Definition quotient_atom_environment i : code_expr :=
  match i with 0 => CEvar 2 | 1 => CEvar 0 | _ => CEvar 1 end.

Definition quotient_member_template :=
  template_set_formula quotient_atom_environment (CEvar 3) (source_dmem $0 $1 $2).
Definition quotient_equal_template :=
  template_set_formula quotient_atom_environment (CEvar 3) (source_deqv $0 $1 $2).
Definition quotient_universal_template :=
  E_wal (CEvar 0) (E_wim (E_wel (CEvar 2) (CEvar 0)) (CEvar 1)).

Definition quotient_fold_spec : SyntaxFoldSpec :=
  {| fold_zero := CEconst 0;
     fold_member := quotient_member_template;
     fold_equal := quotient_equal_template;
     fold_universal := quotient_universal_template |}.

Print Assumptions quotient_fold_spec.

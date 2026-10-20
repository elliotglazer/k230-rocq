(** * Std_dB: named wffs (Logic.v) -> de Bruijn formulas of the Undecidability library.
    [dB rho a]: [rho] maps named variables to terms; generic in the function signature so the same
    translation serves minZF (no function symbols) and ZF (Skolem symbols). *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Core Syntax.Facts Deduction.FullNDFacts Sets.Signatures.
From OldZF Require Import Logic.
Import FullSyntax.
Import ListNotations.
Import Vector.VectorNotations.

Section dB.
Context {Σf : funcs_signature}.
Local Existing Instance ZFSignature.ZF_pred_sig.
Local Existing Instance full_operators.

Definition shift_env (x : nat) (rho : nat -> term) : nat -> term :=
  fun v => if Nat.eqb v x then var 0 else (rho v)`[↑].

Arguments shift_env : simpl never.

Fixpoint dB (rho : nat -> term) (a : wff) : form falsity_on :=
  match a with
  | Weq x y => atom equal ([rho x; rho y])
  | Wel x y => atom elem ([rho x; rho y])
  | Wim a b => bin Impl (dB rho a) (dB rho b)
  | Wn a => bin Impl (dB rho a) falsity
  | Wal x a => quant All (dB (shift_env x rho) a)
  end.

Lemma dB_ext rho rho' a : (forall v, rho v = rho' v) -> dB rho a = dB rho' a.
Proof.
  revert rho rho'; induction a; intros rho rho' H; cbn.
  - now rewrite !H.
  - now rewrite !H.
  - now rewrite (IHa1 rho rho'), (IHa2 rho rho').
  - now rewrite (IHa rho rho').
  - f_equal. apply IHa. intros v. unfold shift_env. now rewrite H.
Qed.

Lemma dB_subst rho sigma a : (dB rho a)[sigma] = dB (rho >> subst_term sigma) a.
Proof.
  revert rho sigma; induction a; intros rho sigma; cbn.
  - reflexivity.
  - reflexivity.
  - now rewrite IHa1, IHa2.
  - now rewrite IHa.
  - f_equal. rewrite IHa. apply dB_ext. intros v. unfold shift_env, funcomp.
    destruct (Nat.eqb v x); cbn; [reflexivity|]. apply up_term.
Qed.
End dB.

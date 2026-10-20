(** * Z_cl: definable power set via closure under finitely many Delta_0 operations.

    Environments (assignments) are finite functions e : n → A; extending e by v appends v at
    position dom e ([Ext0]).  The operations (all Delta_0, [Op k a b c y] = "y = op_k(a,b,c)"):
      0 {a,b}   1 ⋃a   2 a − b   3 {e ⊕ v | e ∈ a, v ∈ b}   4 {e ∈ a | ∃v∈c. e ⊕ v ∈ b}
      5 {x ∈ c | b ⊕ x ∈ a}   6 {e ∈ a | e(b) ∈ e(c)}   7 {e ∈ a | e(b) = e(c)}
    [Cl B C]: C is the closure of B under the operations (⋃ of the ω-iteration of [Step]).
    [Def0 A D]: D = Cl(A ∪ {A}) ∩ P(A).  Only "every definable subset of A is in D" is needed
    ([definable]); the converse is never used.  All definitions are Sigma. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

(** z = e ∪ {(dom e, v)} *)
Definition Ext0 (e v z : term) : form :=
  ∃ ($0 ∈' z`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧
      (OP0 $0 v`[↑]`[↑]`[↑] $2 ∧ Dom0 e`[↑]`[↑]`[↑] $0 ∧
      (∀ ($0 ∈' z`[↑]`[↑]`[↑]`[↑] → $0 ∈' e`[↑]`[↑]`[↑]`[↑] ∨ $0 ≡' $3)) ∧ Sub0 e`[↑]`[↑]`[↑] z`[↑]`[↑]`[↑])))).
(** ∃v∈A. e ⊕ v ∈ R *)
Definition PJ (R A e : term) : form := ∃ ($0 ∈' A`[↑] ∧ ∃ ($0 ∈' R`[↑]`[↑] ∧ Ext0 e`[↑]`[↑] $1 $0)).
(** s ⊕ x ∈ R *)
Definition SC (R s x : term) : form := ∃ ($0 ∈' R`[↑] ∧ Ext0 s`[↑] x`[↑] $0).
(** e(i) ∈ e(j), resp. e(i) = e(j) *)
Definition AI (i j e : term) : form :=
  ∃ ($0 ∈' e`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ (OP0 i`[↑]`[↑]`[↑] $0 $2 ∧
    ∃ ($0 ∈' e`[↑]`[↑]`[↑]`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ (OP0 j`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] $0 $2 ∧ $3 ∈' $0)))))))).
Definition AE (i j e : term) : form :=
  ∃ ($0 ∈' e`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ (OP0 i`[↑]`[↑]`[↑] $0 $2 ∧
    ∃ ($0 ∈' e`[↑]`[↑]`[↑]`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ (OP0 j`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] $0 $2 ∧ $3 ≡' $0)))))))).
(** y = {e ∈ a | P e} for a Delta_0 property P (given as a function of e) *)
Definition SepOf (a y : term) (P : term -> form) : form :=
  (∀ ($0 ∈' y`[↑] → $0 ∈' a`[↑] ∧ P $0)) ∧ ∀ ($0 ∈' a`[↑] → P $0 → $0 ∈' y`[↑]).

(** y = op_k(a, b, c) *)
Definition Op (k : nat) (a b c y : term) : form :=
  match k with
  | 0 => Pair0 a b y
  | 1 => Union0 a y
  | 2 => SepOf a y (fun e => e ∈' b`[↑] → ⊥)
  | 3 => (∀ ($0 ∈' y`[↑] → ∃ ($0 ∈' a`[↑]`[↑] ∧ ∃ ($0 ∈' b`[↑]`[↑]`[↑] ∧ Ext0 $1 $0 $2)))) ∧
         ∀ ($0 ∈' a`[↑] → ∀ ($0 ∈' b`[↑]`[↑] → ∃ ($0 ∈' y`[↑]`[↑]`[↑] ∧ Ext0 $2 $1 $0)))
  | 4 => SepOf a y (fun e => PJ b`[↑] c`[↑] e)
  | 5 => SepOf c y (fun x => SC a`[↑] b`[↑] x)
  | 6 => SepOf a y (fun e => AI b`[↑] c`[↑] e)
  | 7 => SepOf a y (fun e => AE b`[↑] c`[↑] e)
  | _ => ⊥
  end.

Definition Ops (a b c y : term) : form :=
  Op 0 a b c y ∨ Op 1 a b c y ∨ Op 2 a b c y ∨ Op 3 a b c y ∨ Op 4 a b c y ∨ Op 5 a b c y ∨
  Op 6 a b c y ∨ Op 7 a b c y.
Definition OpsIn (Y a b c : term) : form :=
  (∃ ($0 ∈' Y`[↑] ∧ Op 0 a`[↑] b`[↑] c`[↑] $0)) ∧ (∃ ($0 ∈' Y`[↑] ∧ Op 1 a`[↑] b`[↑] c`[↑] $0)) ∧
  (∃ ($0 ∈' Y`[↑] ∧ Op 2 a`[↑] b`[↑] c`[↑] $0)) ∧ (∃ ($0 ∈' Y`[↑] ∧ Op 3 a`[↑] b`[↑] c`[↑] $0)) ∧
  (∃ ($0 ∈' Y`[↑] ∧ Op 4 a`[↑] b`[↑] c`[↑] $0)) ∧ (∃ ($0 ∈' Y`[↑] ∧ Op 5 a`[↑] b`[↑] c`[↑] $0)) ∧
  (∃ ($0 ∈' Y`[↑] ∧ Op 6 a`[↑] b`[↑] c`[↑] $0)) ∧ (∃ ($0 ∈' Y`[↑] ∧ Op 7 a`[↑] b`[↑] c`[↑] $0)).
(** Y = X ∪ {op_k(a,b,c) | a,b,c ∈ X, k < 8} *)
Definition Step (X Y : term) : form :=
  Sub0 X Y ∧
  (∀ ($0 ∈' Y`[↑] → $0 ∈' X`[↑] ∨
       ∃ ($0 ∈' X`[↑]`[↑] ∧ ∃ ($0 ∈' X`[↑]`[↑]`[↑] ∧ ∃ ($0 ∈' X`[↑]`[↑]`[↑]`[↑] ∧ Ops $2 $1 $0 $3))))) ∧
  ∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] → ∀ ($0 ∈' X`[↑]`[↑]`[↑] → OpsIn Y`[↑]`[↑]`[↑] $2 $1 $0))).

(** recursion step for the closure: f = $0, ξ = $1, v = $2, B = $3 *)
Definition Scl : form :=
  (Emp0 $1 → $2 ≡' $3) ∧ (∀ ($0 ∈' $2 → Succ0 $0 $2 → ∃ (App0 $2 $1 $0 ∧ Step $0 $4))) ∧ (Lim0 $1 → Emp0 $2).
(** C = ⋃ ran g *)
Definition RanU (g C : term) : form :=
  (∀ ($0 ∈' C`[↑] → ∃ ($0 ∈' g`[↑]`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ ($3 ∈' $0 ∧
       ∃ ($0 ∈' $3 ∧ ∃ ($0 ∈' $1 ∧ OP0 $0 $2 $4)))))))) ∧
  PairsAll g (Sub0 $0 C`[↑]`[↑]).
(** C = Cl(B) *)
Definition Cl (B C : term) : form :=
  ∃ (∃ (Om0 $1 ∧ Fun0 $0 ∧ Dom0 $0 $1 ∧ RecOK Scl B`[↑]`[↑] $0 ∧ RanU $0 C`[↑]`[↑])).
(** D = Cl(A ∪ {A}) ∩ P(A) *)
Definition Def0 (A D : term) : form :=
  ∃ (∃ (Succ0 A`[↑]`[↑] $1 ∧ Cl $1 $0 ∧ (∀ ($0 ∈' D`[↑]`[↑]`[↑] → $0 ∈' $1 ∧ Sub0 $0 A`[↑]`[↑]`[↑])) ∧
        ∀ ($0 ∈' $1 → Sub0 $0 A`[↑]`[↑]`[↑] → $0 ∈' D`[↑]`[↑]`[↑]))).

#[global] Arguments Ext0 : simpl never.
#[global] Arguments PJ : simpl never.
#[global] Arguments SC : simpl never.
#[global] Arguments AI : simpl never.
#[global] Arguments AE : simpl never.
#[global] Arguments SepOf : simpl never.
#[global] Arguments Op : simpl never.
#[global] Arguments Ops : simpl never.
#[global] Arguments OpsIn : simpl never.
#[global] Arguments Step : simpl never.
#[global] Arguments RanU : simpl never.
#[global] Arguments Cl : simpl never.
#[global] Arguments Def0 : simpl never.

Lemma Ext0_subst e v z sg : (Ext0 e v z)[sg] = Ext0 e`[sg] v`[sg] z`[sg].
Proof. psubst Ext0. Qed.
#[global] Hint Rewrite Ext0_subst : fsub.
Lemma PJ_subst R A e sg : (PJ R A e)[sg] = PJ R`[sg] A`[sg] e`[sg].
Proof. psubst PJ. Qed.
Lemma SC_subst R s x sg : (SC R s x)[sg] = SC R`[sg] s`[sg] x`[sg].
Proof. psubst SC. Qed.
Lemma AI_subst i j e sg : (AI i j e)[sg] = AI i`[sg] j`[sg] e`[sg].
Proof. psubst AI. Qed.
Lemma AE_subst i j e sg : (AE i j e)[sg] = AE i`[sg] j`[sg] e`[sg].
Proof. psubst AE. Qed.
#[global] Hint Rewrite PJ_subst SC_subst AI_subst AE_subst : fsub.
Lemma Op_subst k a b c y sg : (Op k a b c y)[sg] = Op k a`[sg] b`[sg] c`[sg] y`[sg].
Proof.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; unfold Op, SepOf; cbn; autorewrite with fsub; cbn;
    autorewrite with fsub; fix_up; reflexivity.
Qed.
#[global] Hint Rewrite Op_subst : fsub.
Lemma Ops_subst a b c y sg : (Ops a b c y)[sg] = Ops a`[sg] b`[sg] c`[sg] y`[sg].
Proof. unfold Ops. cbn. now autorewrite with fsub. Qed.
Lemma OpsIn_subst Y a b c sg : (OpsIn Y a b c)[sg] = OpsIn Y`[sg] a`[sg] b`[sg] c`[sg].
Proof. unfold OpsIn. cbn. autorewrite with fsub. cbn. now autorewrite with fsub. Qed.
#[global] Hint Rewrite Ops_subst OpsIn_subst : fsub.
Lemma Step_subst X Y sg : (Step X Y)[sg] = Step X`[sg] Y`[sg].
Proof. unfold Step. cbn. autorewrite with fsub. cbn. fix_up. reflexivity. Qed.
#[global] Hint Rewrite Step_subst : fsub.
Lemma RanU_subst g C sg : (RanU g C)[sg] = RanU g`[sg] C`[sg].
Proof. unfold RanU. cbn. autorewrite with fsub. cbn. fix_up. reflexivity. Qed.
#[global] Hint Rewrite RanU_subst : fsub.
Lemma Cl_subst B C sg : (Cl B C)[sg] = Cl B`[sg] C`[sg].
Proof. unfold Cl. cbn. autorewrite with fsub. cbn. fix_up. reflexivity. Qed.
#[global] Hint Rewrite Cl_subst : fsub.
Lemma Def0_subst A D sg : (Def0 A D)[sg] = Def0 A`[sg] D`[sg].
Proof. unfold Def0. cbn. autorewrite with fsub. cbn. fix_up. reflexivity. Qed.
#[global] Hint Rewrite Def0_subst : fsub.

Ltac unfold_cl := do 3 try unfold Def0, Cl, RanU, RecOK, SR, Scl, Step, OpsIn, Ops, Op, SepOf, Ext0, PJ, SC, AI, AE,
  App0, OP0, Sing0, Pair0, Union0, Emp0, Succ0, Sub0, Lim0, Ord0, Trans0, Om0, Fun0, IsRel0, Dom0, PairsAll.

Lemma fb_Scl : fb 4 Scl.
Proof. fbcomp. Qed.

#[local] Hint Rewrite @relS_subst : fsub.


(** ** Instances used by this file *)
(** [UF F] (x = $0, y = $1, parameters $2..): y = {z | F(z, x, params)}, where F has z = $0, x = $1,
    parameters $2.. ; used with replacement to form ⋃_{x ∈ X} {z | F(z, x)} *)
Definition UF (F : form) : form := ∀ ($0 ∈' $2 ↔ F[$0 .: $1 .: (fun k => $(3 + k))]).
(** stages below n are contained in stage n *)
Definition Mono (n g : term) : form :=
  ∀ ($0 ∈' n`[↑] → ∀ (∀ (App0 g`[↑]`[↑]`[↑] $2 $1 → App0 g`[↑]`[↑]`[↑] n`[↑]`[↑]`[↑] $0 → Sub0 $1 $0))).
#[global] Arguments Mono : simpl never.
Lemma Mono_subst n g sg : (Mono n g)[sg] = Mono n`[sg] g`[sg].
Proof. psubst Mono. Qed.
#[global] Hint Rewrite Mono_subst : fsub.

Fixpoint OpsUp (k : nat) (a b c y : term) : form :=
  match k with 0 => Op 0 a b c y | S k' => OpsUp k' a b c y ∨ Op (S k') a b c y end.
Lemma OpsUp_subst k a b c y sg : (OpsUp k a b c y)[sg] = OpsUp k a`[sg] b`[sg] c`[sg] y`[sg].
Proof. induction k as [|k IH]; cbn; [now rewrite Op_subst | now rewrite IH, Op_subst]. Qed.
#[local] Hint Rewrite OpsUp_subst : fsub.
Lemma Ops_up a b c y : Ops a b c y = OpsUp 7 a b c y.
Proof. reflexivity. Qed.

(** a fast replacement for [simp]: rewrite only the substitution lemmas whose left side occurs *)
Local Ltac fsz_g := match goal with
  | |- context [ (Ext0 ?x0 ?x1 ?x2)[?s] ] => rewrite (Ext0_subst x0 x1 x2 s)
  | |- context [ (PJ ?x0 ?x1 ?x2)[?s] ] => rewrite (PJ_subst x0 x1 x2 s)
  | |- context [ (SC ?x0 ?x1 ?x2)[?s] ] => rewrite (SC_subst x0 x1 x2 s)
  | |- context [ (AI ?x0 ?x1 ?x2)[?s] ] => rewrite (AI_subst x0 x1 x2 s)
  | |- context [ (AE ?x0 ?x1 ?x2)[?s] ] => rewrite (AE_subst x0 x1 x2 s)
  | |- context [ (Op ?x0 ?x1 ?x2 ?x3 ?x4)[?s] ] => rewrite (Op_subst x0 x1 x2 x3 x4 s)
  | |- context [ (Ops ?x0 ?x1 ?x2 ?x3)[?s] ] => rewrite (Ops_subst x0 x1 x2 x3 s)
  | |- context [ (OpsIn ?x0 ?x1 ?x2 ?x3)[?s] ] => rewrite (OpsIn_subst x0 x1 x2 x3 s)
  | |- context [ (Step ?x0 ?x1)[?s] ] => rewrite (Step_subst x0 x1 s)
  | |- context [ (RanU ?x0 ?x1)[?s] ] => rewrite (RanU_subst x0 x1 s)
  | |- context [ (Cl ?x0 ?x1)[?s] ] => rewrite (Cl_subst x0 x1 s)
  | |- context [ (Def0 ?x0 ?x1)[?s] ] => rewrite (Def0_subst x0 x1 s)
  | |- context [ (Mono ?x0 ?x1)[?s] ] => rewrite (Mono_subst x0 x1 s)
  | |- context [ (OpsUp ?x0 ?x1 ?x2 ?x3 ?x4)[?s] ] => rewrite (OpsUp_subst x0 x1 x2 x3 x4 s)
  | |- context [ (SR ?x0 ?x1 ?x2 ?x3 ?x4)[?s] ] => rewrite (SR_subst x0 x1 x2 x3 x4 s)
  | |- context [ (RecOK ?x0 ?x1 ?x2)[?s] ] => rewrite (RecOK_subst x0 x1 x2 s)
  | |- context [ (Agree ?x0 ?x1 ?x2)[?s] ] => rewrite (Agree_subst x0 x1 x2 s)
  | |- context [ (Dom0 ?x0 ?x1)[?s] ] => rewrite (Dom0_subst x0 x1 s)
  | |- context [ (Fun0 ?x0)[?s] ] => rewrite (Fun0_subst x0 s)
  | |- context [ (IsRel0 ?x0)[?s] ] => rewrite (IsRel0_subst x0 s)
  | |- context [ (PairsAll ?x0 ?x1)[?s] ] => rewrite (PairsAll_subst x0 x1 s)
  | |- context [ (App0 ?x0 ?x1 ?x2)[?s] ] => rewrite (App0_subst x0 x1 x2 s)
  | |- context [ (Union0 ?x0 ?x1)[?s] ] => rewrite (Union0_subst x0 x1 s)
  | |- context [ (Om0 ?x0)[?s] ] => rewrite (Om0_subst x0 s)
  | |- context [ (Lim0 ?x0)[?s] ] => rewrite (Lim0_subst x0 s)
  | |- context [ (Succ0 ?x0 ?x1)[?s] ] => rewrite (Succ0_subst x0 x1 s)
  | |- context [ (Ord0 ?x0)[?s] ] => rewrite (Ord0_subst x0 s)
  | |- context [ (Trans0 ?x0)[?s] ] => rewrite (Trans0_subst x0 s)
  | |- context [ (Sub0 ?x0 ?x1)[?s] ] => rewrite (Sub0_subst x0 x1 s)
  | |- context [ (Emp0 ?x0)[?s] ] => rewrite (Emp0_subst x0 s)
  | |- context [ (OP0 ?x0 ?x1 ?x2)[?s] ] => rewrite (OP0_subst x0 x1 x2 s)
  | |- context [ (Pair0 ?x0 ?x1 ?x2)[?s] ] => rewrite (Pair0_subst x0 x1 x2 s)
  | |- context [ (Sing0 ?x0 ?x1)[?s] ] => rewrite (Sing0_subst x0 x1 s)
  | |- context [ (App ?x0 ?x1 ?x2)[?s] ] => rewrite (App_subst x0 x1 x2 s)
  | |- context [ (OP ?x0 ?x1 ?x2)[?s] ] => rewrite (OP_subst x0 x1 x2 s)
  | |- context [ (Adj ?x0 ?x1 ?x2)[?s] ] => rewrite (Adj_subst x0 x1 x2 s)
  | |- context [ (BUn ?x0 ?x1 ?x2)[?s] ] => rewrite (BUn_subst x0 x1 x2 s)
  | |- context [ (Sing ?x0 ?x1)[?s] ] => rewrite (Sing_subst x0 x1 s)
  | |- context [ (is_om ?x0)[?s] ] => rewrite (is_om_subst x0 s)
  | |- context [ (is_inductive ?x0)[?s] ] => rewrite (is_inductive_subst x0 s)
  | |- context [ (is_sigma ?x0 ?x1)[?s] ] => rewrite (is_sigma_subst x0 x1 s)
  | |- context [ (is_power ?x0 ?x1)[?s] ] => rewrite (is_power_subst x0 x1 s)
  | |- context [ (is_union ?x0 ?x1)[?s] ] => rewrite (is_union_subst x0 x1 s)
  | |- context [ (is_pair ?x0 ?x1 ?x2)[?s] ] => rewrite (is_pair_subst x0 x1 x2 s)
  | |- context [ (is_eset ?x0)[?s] ] => rewrite (is_eset_subst x0 s)
  | |- context [ (sub' ?x0 ?x1)[?s] ] => rewrite (sub'_subst x0 x1 s)
  | |- context [ (relS ?Y ?p)[?s] ] => rewrite (relS_subst p Y s)
  | |- context [ ?p[up ?s][?t..] ] => rewrite (up_inst_form p s t)
  | |- context [ ?p[↑][?t .: ?s] ] => rewrite (shift_scons_form p t s)
  | |- context [ ?p[↑][up ?s] ] => rewrite (up_form_comm p s)
  | |- context [ ?p[var] ] => rewrite (subst_var p)
  | |- context [ ?t`[↑]`[?u .: ?s] ] => rewrite (shift_scons_term t u s)
  | |- context [ ?t`[↑]`[up ?s] ] => rewrite (up_term t s)
  | |- context [ ?t`[var] ] => rewrite (subst_term_var t)
  end.
Local Ltac fsz_h H := match type of H with
  | context [ (Ext0 ?x0 ?x1 ?x2)[?s] ] => rewrite (Ext0_subst x0 x1 x2 s) in H
  | context [ (PJ ?x0 ?x1 ?x2)[?s] ] => rewrite (PJ_subst x0 x1 x2 s) in H
  | context [ (SC ?x0 ?x1 ?x2)[?s] ] => rewrite (SC_subst x0 x1 x2 s) in H
  | context [ (AI ?x0 ?x1 ?x2)[?s] ] => rewrite (AI_subst x0 x1 x2 s) in H
  | context [ (AE ?x0 ?x1 ?x2)[?s] ] => rewrite (AE_subst x0 x1 x2 s) in H
  | context [ (Op ?x0 ?x1 ?x2 ?x3 ?x4)[?s] ] => rewrite (Op_subst x0 x1 x2 x3 x4 s) in H
  | context [ (Ops ?x0 ?x1 ?x2 ?x3)[?s] ] => rewrite (Ops_subst x0 x1 x2 x3 s) in H
  | context [ (OpsIn ?x0 ?x1 ?x2 ?x3)[?s] ] => rewrite (OpsIn_subst x0 x1 x2 x3 s) in H
  | context [ (Step ?x0 ?x1)[?s] ] => rewrite (Step_subst x0 x1 s) in H
  | context [ (RanU ?x0 ?x1)[?s] ] => rewrite (RanU_subst x0 x1 s) in H
  | context [ (Cl ?x0 ?x1)[?s] ] => rewrite (Cl_subst x0 x1 s) in H
  | context [ (Def0 ?x0 ?x1)[?s] ] => rewrite (Def0_subst x0 x1 s) in H
  | context [ (Mono ?x0 ?x1)[?s] ] => rewrite (Mono_subst x0 x1 s) in H
  | context [ (OpsUp ?x0 ?x1 ?x2 ?x3 ?x4)[?s] ] => rewrite (OpsUp_subst x0 x1 x2 x3 x4 s) in H
  | context [ (SR ?x0 ?x1 ?x2 ?x3 ?x4)[?s] ] => rewrite (SR_subst x0 x1 x2 x3 x4 s) in H
  | context [ (RecOK ?x0 ?x1 ?x2)[?s] ] => rewrite (RecOK_subst x0 x1 x2 s) in H
  | context [ (Agree ?x0 ?x1 ?x2)[?s] ] => rewrite (Agree_subst x0 x1 x2 s) in H
  | context [ (Dom0 ?x0 ?x1)[?s] ] => rewrite (Dom0_subst x0 x1 s) in H
  | context [ (Fun0 ?x0)[?s] ] => rewrite (Fun0_subst x0 s) in H
  | context [ (IsRel0 ?x0)[?s] ] => rewrite (IsRel0_subst x0 s) in H
  | context [ (PairsAll ?x0 ?x1)[?s] ] => rewrite (PairsAll_subst x0 x1 s) in H
  | context [ (App0 ?x0 ?x1 ?x2)[?s] ] => rewrite (App0_subst x0 x1 x2 s) in H
  | context [ (Union0 ?x0 ?x1)[?s] ] => rewrite (Union0_subst x0 x1 s) in H
  | context [ (Om0 ?x0)[?s] ] => rewrite (Om0_subst x0 s) in H
  | context [ (Lim0 ?x0)[?s] ] => rewrite (Lim0_subst x0 s) in H
  | context [ (Succ0 ?x0 ?x1)[?s] ] => rewrite (Succ0_subst x0 x1 s) in H
  | context [ (Ord0 ?x0)[?s] ] => rewrite (Ord0_subst x0 s) in H
  | context [ (Trans0 ?x0)[?s] ] => rewrite (Trans0_subst x0 s) in H
  | context [ (Sub0 ?x0 ?x1)[?s] ] => rewrite (Sub0_subst x0 x1 s) in H
  | context [ (Emp0 ?x0)[?s] ] => rewrite (Emp0_subst x0 s) in H
  | context [ (OP0 ?x0 ?x1 ?x2)[?s] ] => rewrite (OP0_subst x0 x1 x2 s) in H
  | context [ (Pair0 ?x0 ?x1 ?x2)[?s] ] => rewrite (Pair0_subst x0 x1 x2 s) in H
  | context [ (Sing0 ?x0 ?x1)[?s] ] => rewrite (Sing0_subst x0 x1 s) in H
  | context [ (App ?x0 ?x1 ?x2)[?s] ] => rewrite (App_subst x0 x1 x2 s) in H
  | context [ (OP ?x0 ?x1 ?x2)[?s] ] => rewrite (OP_subst x0 x1 x2 s) in H
  | context [ (Adj ?x0 ?x1 ?x2)[?s] ] => rewrite (Adj_subst x0 x1 x2 s) in H
  | context [ (BUn ?x0 ?x1 ?x2)[?s] ] => rewrite (BUn_subst x0 x1 x2 s) in H
  | context [ (Sing ?x0 ?x1)[?s] ] => rewrite (Sing_subst x0 x1 s) in H
  | context [ (is_om ?x0)[?s] ] => rewrite (is_om_subst x0 s) in H
  | context [ (is_inductive ?x0)[?s] ] => rewrite (is_inductive_subst x0 s) in H
  | context [ (is_sigma ?x0 ?x1)[?s] ] => rewrite (is_sigma_subst x0 x1 s) in H
  | context [ (is_power ?x0 ?x1)[?s] ] => rewrite (is_power_subst x0 x1 s) in H
  | context [ (is_union ?x0 ?x1)[?s] ] => rewrite (is_union_subst x0 x1 s) in H
  | context [ (is_pair ?x0 ?x1 ?x2)[?s] ] => rewrite (is_pair_subst x0 x1 x2 s) in H
  | context [ (is_eset ?x0)[?s] ] => rewrite (is_eset_subst x0 s) in H
  | context [ (sub' ?x0 ?x1)[?s] ] => rewrite (sub'_subst x0 x1 s) in H
  | context [ (relS ?Y ?p)[?s] ] => rewrite (relS_subst p Y s) in H
  | context [ ?p[up ?s][?t..] ] => rewrite (up_inst_form p s t) in H
  | context [ ?p[↑][?t .: ?s] ] => rewrite (shift_scons_form p t s) in H
  | context [ ?p[↑][up ?s] ] => rewrite (up_form_comm p s) in H
  | context [ ?p[var] ] => rewrite (subst_var p) in H
  | context [ ?t`[↑]`[?u .: ?s] ] => rewrite (shift_scons_term t u s) in H
  | context [ ?t`[↑]`[up ?s] ] => rewrite (up_term t s) in H
  | context [ ?t`[var] ] => rewrite (subst_term_var t) in H
  end.
Local Ltac fsz_xg := fail.
Local Ltac fsz_xh H := fail.
Local Ltac simp ::= cbn; repeat (first [fsz_g | fsz_xg]); cbn; repeat (first [fsz_g | fsz_xg]); fix_up.
Local Ltac simp_in H ::= cbn in H; repeat (first [fsz_h H | fsz_xh H]); cbn in H; repeat (first [fsz_h H | fsz_xh H]);
  fix_up_in H.


Definition S_neg : form := ¬ ($0 ∈' $1).
Definition S_pj : form := PJ $1 $2 $0.
Definition S_sc : form := SC $1 $2 $0.
Definition S_ai : form := AI $1 $2 $0.
Definition S_ae : form := AE $1 $2 $0.
Definition S_dom : form := ∃ App0 $2 $1 $0.
Definition S_ran : form := ∃ (∃ (App0 $3 $1 $0 ∧ $2 ∈' $0)).
Definition S_sub : form := Sub0 $0 $1.
Definition S_mono : form := Mono $0 $1.
Definition F_ext : form := Ext0 $2 $1 $0.
Definition F_op3 : form := ∃ ($0 ∈' $3 ∧ Ext0 $2 $0 $1).
Definition F_s1 : form := Ops $2 $3 $1 $0.
Definition F_s2 : form := ∃ ($0 ∈' $4 ∧ Ops $3 $2 $0 $1).
Definition F_s3 : form := ∃ ($0 ∈' $3 ∧ ∃ ($0 ∈' $4 ∧ Ops $3 $1 $0 $2)).

Definition cl_insts : list form :=
  [forall_times 1 (ax_sep' S_neg); forall_times 2 (ax_sep' S_pj); forall_times 2 (ax_sep' S_sc);
   forall_times 2 (ax_sep' S_ai); forall_times 2 (ax_sep' S_ae); forall_times 1 (ax_sep' S_dom);
   forall_times 1 (ax_sep' S_ran); forall_times 1 (ax_sep' S_sub); forall_times 1 (ax_sep' S_mono);
   forall_times 1 (ax_rep' (UF F_ext)); forall_times 1 (ax_rep' (UF F_op3));
   forall_times 2 (ax_rep' (UF F_s1)); forall_times 2 (ax_rep' (UF F_s2)); forall_times 1 (ax_rep' (UF F_s3))].

Lemma cl_insts_ok a : In a cl_insts -> ZFR a.
Proof.
  intros H. repeat (destruct H as [<-|H]; [first [apply ZFR_sep | apply ZFR_rep]; fbcomp|]). destruct H.
Qed.

(** fixed instances used by this file; includes Ax_ord and rec_insts Scl *)
Definition Ax_cl : list form := Ax_ord ++ rec_insts Scl ++ cl_insts.
Lemma Ax_cl_ok a : In a Ax_cl -> ZFR a.
Proof.
  intros [H|H]%in_app_iff; [now apply Ax_ord_ok|].
  apply in_app_iff in H as [H|H]; [exact (rec_insts_ok Scl a fb_Scl H) | exact (cl_insts_ok a H)].
Qed.
Lemma Ax_cl_ord G : incl Ax_cl G -> incl Ax_ord G.
Proof. intros H a Ha. apply H, in_app_iff. now left. Qed.
Lemma Ax_cl_rec G : incl Ax_cl G -> incl (rec_insts Scl) G.
Proof. intros H a Ha. apply H, in_app_iff. right. apply in_app_iff. now left. Qed.
Lemma Ax_cl_in G a : incl Ax_cl G -> In a cl_insts -> In a G.
Proof. intros H Ha. apply H, in_app_iff. right. apply in_app_iff. now right. Qed.

Local Tactic Notation "clin" int_or_var(k) := intros; eapply Ax_cl_in; [eassumption|]; cbn; do k right; now left.
Lemma in_S_neg G : incl Ax_cl G -> In (forall_times 1 (ax_sep' S_neg)) G. Proof. clin 0. Qed.
Lemma in_S_pj G : incl Ax_cl G -> In (forall_times 2 (ax_sep' S_pj)) G. Proof. clin 1. Qed.
Lemma in_S_sc G : incl Ax_cl G -> In (forall_times 2 (ax_sep' S_sc)) G. Proof. clin 2. Qed.
Lemma in_S_ai G : incl Ax_cl G -> In (forall_times 2 (ax_sep' S_ai)) G. Proof. clin 3. Qed.
Lemma in_S_ae G : incl Ax_cl G -> In (forall_times 2 (ax_sep' S_ae)) G. Proof. clin 4. Qed.
Lemma in_S_dom G : incl Ax_cl G -> In (forall_times 1 (ax_sep' S_dom)) G. Proof. clin 5. Qed.
Lemma in_S_ran G : incl Ax_cl G -> In (forall_times 1 (ax_sep' S_ran)) G. Proof. clin 6. Qed.
Lemma in_S_sub G : incl Ax_cl G -> In (forall_times 1 (ax_sep' S_sub)) G. Proof. clin 7. Qed.
Lemma in_S_mono G : incl Ax_cl G -> In (forall_times 1 (ax_sep' S_mono)) G. Proof. clin 8. Qed.
Lemma in_F_ext G : incl Ax_cl G -> In (forall_times 1 (ax_rep' (UF F_ext))) G. Proof. clin 9. Qed.
Lemma in_F_op3 G : incl Ax_cl G -> In (forall_times 1 (ax_rep' (UF F_op3))) G. Proof. clin 10. Qed.
Lemma in_F_s1 G : incl Ax_cl G -> In (forall_times 2 (ax_rep' (UF F_s1))) G. Proof. clin 11. Qed.
Lemma in_F_s2 G : incl Ax_cl G -> In (forall_times 2 (ax_rep' (UF F_s2))) G. Proof. clin 12. Qed.
Lemma in_F_s3 G : incl Ax_cl G -> In (forall_times 1 (ax_rep' (UF F_s3))) G. Proof. clin 13. Qed.

(** ** Wrappers around the upstream lemmas (insulate against changes of their section variables) *)
Local Ltac pre := match goal with HC : incl Ax_cl ?G |- _ =>
  let HO := fresh "HO" in let HP := fresh "HP" in
  pose proof (Ax_cl_ord _ HC) as HO; pose proof (Ax_ord_prim _ HO) as HP end.
Local Ltac wr L := intros; pre; eapply L; eassumption.

Section W.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).
Lemma u_emp0_ex : G ⊢C ∃ Emp0 $0. Proof. wr @emp0_ex. Qed.
Lemma u_pair0_ex x y : G ⊢C ∃ Pair0 x`[↑] y`[↑] $0. Proof. wr @pair0_ex. Qed.
Lemma u_op0_ex x y : G ⊢C ∃ OP0 x`[↑] y`[↑] $0. Proof. wr @op0_ex. Qed.
Lemma u_succ0_ex x : G ⊢C ∃ Succ0 x`[↑] $0. Proof. wr @succ0_ex. Qed.
Lemma u_union0_ex x : G ⊢C ∃ Union0 x`[↑] $0. Proof. wr @union0_ex. Qed.
Lemma u_emp0_unique e e' : G ⊢C Emp0 e -> G ⊢C Emp0 e' -> G ⊢C e ≡' e'. Proof. wr @emp0_unique. Qed.
Lemma u_op0_unique x y p p' : G ⊢C OP0 x y p -> G ⊢C OP0 x y p' -> G ⊢C p ≡' p'. Proof. wr @op0_unique. Qed.
Lemma u_succ0_unique x s s' : G ⊢C Succ0 x s -> G ⊢C Succ0 x s' -> G ⊢C s ≡' s'. Proof. wr @succ0_unique. Qed.
Lemma u_union0_unique x u u' : G ⊢C Union0 x u -> G ⊢C Union0 x u' -> G ⊢C u ≡' u'. Proof. wr @union0_unique. Qed.
Lemma u_op0_inj x y x' y' p : G ⊢C OP0 x y p -> G ⊢C OP0 x' y' p -> G ⊢C x ≡' x' ∧ y ≡' y'.
Proof. wr @op0_inj. Qed.
Lemma u_op0_comp x y p : G ⊢C OP0 x y p ->
  G ⊢C (∃ ($0 ∈' p`[↑] ∧ x`[↑] ∈' $0)) ∧ ∃ ($0 ∈' p`[↑] ∧ y`[↑] ∈' $0).
Proof. wr @op0_comp. Qed.
Lemma u_pairsall_use f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].
Proof.
  intros H1 H2. pre.
  first [ exact (pairsall_use HG HP f B u v H1 H2) | exact (pairsall_use HG f B u v H1 H2) ].
Qed.
Lemma u_pairsall_intro f B :
  (forall G' u v, incl G G' -> G' ⊢C App0 f u v -> G' ⊢C B[v .: u .: var]) -> G ⊢C PairsAll f B.
Proof. wr @pairsall_intro. Qed.
Lemma u_fun0_app f u v v' : G ⊢C Fun0 f -> G ⊢C App0 f u v -> G ⊢C App0 f u v' -> G ⊢C v ≡' v'.
Proof. wr @fun0_app. Qed.
Lemma u_dom0_app f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.
Proof. wr @dom0_app. Qed.
Lemma u_dom0_in f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.
Proof. wr @dom0_in. Qed.
Lemma u_app0_intro f u v p : G ⊢C OP0 u v p -> G ⊢C p ∈' f -> G ⊢C App0 f u v.
Proof. wr @app0_intro. Qed.

Lemma u_no_self x : G ⊢C x ∈' x -> G ⊢C ⊥. Proof. wr @no_self. Qed.
Lemma u_no_cycle2 x y : G ⊢C x ∈' y -> G ⊢C y ∈' x -> G ⊢C ⊥. Proof. wr @no_cycle2. Qed.
Lemma u_ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x. Proof. wr @ord_el. Qed.
Lemma u_ord_tri a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C a ∈' b ∨ a ≡' b ∨ b ∈' a. Proof. wr @ord_tri. Qed.
Lemma u_ord_cases a : G ⊢C Ord0 a -> G ⊢C Emp0 a ∨ (∃ (Ord0 $0 ∧ Succ0 $0 a`[↑])) ∨ Lim0 a.
Proof. wr @ord_cases. Qed.
Lemma u_om_ex : G ⊢C ∃ Om0 $0. Proof. wr @om_ex. Qed.
Lemma u_om_unique w w' : G ⊢C Om0 w -> G ⊢C Om0 w' -> G ⊢C w ≡' w'. Proof. wr @om_unique. Qed.
Lemma u_om_ord w : G ⊢C Om0 w -> G ⊢C Ord0 w. Proof. wr @om_ord. Qed.
Lemma u_om_emp w e : G ⊢C Om0 w -> G ⊢C Emp0 e -> G ⊢C e ∈' w. Proof. wr @om_emp. Qed.
Lemma u_om_succ w n s : G ⊢C Om0 w -> G ⊢C n ∈' w -> G ⊢C Succ0 n s -> G ⊢C s ∈' w. Proof. wr @om_succ. Qed.
Lemma u_om_ind w X : G ⊢C Om0 w -> G ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  G ⊢C ∀ ($0 ∈' w`[↑] → $0 ∈' X`[↑] → ∀ (Succ0 $1 $0 → $0 ∈' X`[↑]`[↑])) ->
  G ⊢C Sub0 w X.
Proof. wr @om_ind. Qed.
End W.

(** ** Basic facts about the Delta_0 primitives *)
Section Basic.
Context {G : list form} (HG : incl ZF0base G).

Lemma sub0_use x y z : G ⊢C Sub0 x y -> G ⊢C z ∈' x -> G ⊢C z ∈' y.
Proof. intros H Hz. unfold Sub0 in H. finst H z. exact (IE H Hz). Qed.
Lemma emp0_el e z : G ⊢C Emp0 e -> G ⊢C z ∈' e -> G ⊢C ⊥.
Proof. intros H Hz. unfold Emp0 in H. finst H z. exact (IE H Hz). Qed.
Lemma pair0_l x y p : G ⊢C Pair0 x y p -> G ⊢C x ∈' p.
Proof. intros H. unfold Pair0 in H. exact (CE1 (CE1 H)). Qed.
Lemma pair0_r x y p : G ⊢C Pair0 x y p -> G ⊢C y ∈' p.
Proof. intros H. unfold Pair0 in H. exact (CE2 (CE1 H)). Qed.
Lemma pair0_el x y p z : G ⊢C Pair0 x y p -> G ⊢C z ∈' p -> G ⊢C z ≡' x ∨ z ≡' y.
Proof. intros H Hz. unfold Pair0 in H. pose proof (CE2 H) as H2. finst H2 z. exact (IE H2 Hz). Qed.
Lemma union0_el x u z : G ⊢C Union0 x u -> G ⊢C z ∈' u -> G ⊢C ∃ ($0 ∈' x`[↑] ∧ z`[↑] ∈' $0).
Proof. intros H Hz. unfold Union0 in H. pose proof (CE1 H) as H1. finst H1 z. exact (IE H1 Hz). Qed.
Lemma union0_in x u w z : G ⊢C Union0 x u -> G ⊢C w ∈' x -> G ⊢C z ∈' w -> G ⊢C z ∈' u.
Proof.
  intros H Hw Hz. unfold Union0 in H. pose proof (CE2 H) as H2. finst H2 w. fmp H2 Hw. finst H2 z.
  exact (IE H2 Hz).
Qed.
Lemma succ0_self x s : G ⊢C Succ0 x s -> G ⊢C x ∈' s.
Proof. intros H. unfold Succ0 in H. exact (CE1 (CE1 H)). Qed.
Lemma succ0_sub x s : G ⊢C Succ0 x s -> G ⊢C Sub0 x s.
Proof. intros H. unfold Succ0 in H. exact (CE2 (CE1 H)). Qed.
Lemma succ0_el x s z : G ⊢C Succ0 x s -> G ⊢C z ∈' s -> G ⊢C z ∈' x ∨ z ≡' x.
Proof. intros H Hz. unfold Succ0 in H. pose proof (CE2 H) as H2. finst H2 z. exact (IE H2 Hz). Qed.

(** SepOf, for an arbitrary property P *)
Lemma sepof_iff a y P : G ⊢C SepOf a y P -> G ⊢C ∀ ($0 ∈' y`[↑] ↔ $0 ∈' a`[↑] ∧ P $0).
Proof.
  intros H. unfold SepOf in H. pose proof (CE1 H) as H1. pose proof (CE2 H) as H2.
  apply AllI_named. intros z. pose proof (AllE z H1) as H1'. pose proof (AllE z H2) as H2'.
  cbn in H1', H2' |- *. apply CI; [exact H1'|]. apply II.
  eapply IE; [eapply IE; [apply weak_cons, H2'|eapply CE1, Ctx; now left]|eapply CE2, Ctx; now left].
Qed.
Lemma sepof_intro a y P : G ⊢C ∀ ($0 ∈' y`[↑] ↔ $0 ∈' a`[↑] ∧ P $0) -> G ⊢C SepOf a y P.
Proof.
  intros H. unfold SepOf. apply CI; apply AllI_named; intros z; pose proof (AllE z H) as H'; cbn in H' |- *.
  - exact (CE1 H').
  - apply II, II. eapply IE; [apply weak_cons, weak_cons, (CE2 H')|]. apply CI; apply Ctx; [right|]; now left.
Qed.
End Basic.


(** weaken every fact about the context A to B, given [Hinc : incl A B] *)
Local Ltac wk Hinc := match type of Hinc with incl ?A ?B =>
  repeat match goal with
  | H : A ⊢C _ |- _ => apply (fun h => Weak h Hinc) in H
  | H : incl ?X A |- _ => apply (fun h => incl_tran h Hinc) in H
  | H : In ?x A |- _ => apply Hinc in H
  end end.

(** ** The eight operations: tools for the disjunction [Ops] and the conjunction [OpsIn] *)
Lemma ops_inj {G} k a b c y : k < 8 -> G ⊢C Op k a b c y -> G ⊢C Ops a b c y.
Proof.
  intros Hk H. unfold Ops.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia; repeat first [exact H | apply DI2; exact H | apply DI1].
Qed.

Lemma or_imp {G} (a b c : form) : G ⊢C a → c -> G ⊢C b → c -> G ⊢C (a ∨ b) → c.
Proof. intros H1 H2. apply II. eapply DE_rule; [apply Ctx; now left|apply weak_cons, H1|apply weak_cons, H2]. Qed.

Lemma ops_elim {G} a b c y psi : (forall k, k < 8 -> G ⊢C Op k a b c y → psi) -> G ⊢C Ops a b c y → psi.
Proof. intros K. unfold Ops. repeat first [apply K; lia | apply or_imp]. Qed.

Lemma opsin_proj {G} k Y a b c : k < 8 -> G ⊢C OpsIn Y a b c ->
  G ⊢C ∃ ($0 ∈' Y`[↑] ∧ Op k a`[↑] b`[↑] c`[↑] $0).
Proof.
  intros Hk H. unfold OpsIn in H.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia; repeat first [exact H | exact (CE2 H) | apply CE1 in H].
Qed.

Lemma opsin_intro {G} Y a b c : (forall k, k < 8 -> G ⊢C ∃ ($0 ∈' Y`[↑] ∧ Op k a`[↑] b`[↑] c`[↑] $0)) ->
  G ⊢C OpsIn Y a b c.
Proof. intros K. unfold OpsIn. repeat apply CI; apply K; lia. Qed.


(** ** Components of ordered pairs *)
Lemma op0_c1 {G} (HG : incl ZF0base G) x y p : G ⊢C OP0 x y p -> G ⊢C ∃ ($0 ∈' p`[↑] ∧ x`[↑] ∈' $0).
Proof.
  intros H. unfold OP0 in H. fdestr H H12 H3. fdestr H12 H1 H2. fex H1 s Hs. fdestr Hs Hs1 Hs2.
  fexists s. fsplit; [exact Hs1|]. unfold Sing0 in Hs2. exact (CE1 Hs2).
Qed.
Lemma op0_c2 {G} (HG : incl ZF0base G) x y p : G ⊢C OP0 x y p -> G ⊢C ∃ ($0 ∈' p`[↑] ∧ y`[↑] ∈' $0).
Proof.
  intros H. unfold OP0 in H. fdestr H H12 H3. fdestr H12 H1 H2. fex H2 s Hs. fdestr Hs Hs1 Hs2.
  fexists s. fsplit; [exact Hs1|exact (pair0_r HG x y s Hs2)].
Qed.

(** ** Domains and the extension e ⊕ v *)
Lemma dom0_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) f d d' : G ⊢C Dom0 f d -> G ⊢C Dom0 f d' -> G ⊢C d ≡' d'.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall u; fintro Hu.
  - fobtain (u_dom0_app HG HR HOm HC f d u H1 Hu) as v Hv. exact (u_dom0_in HG HR HOm HC f d' u v H2 Hv).
  - fobtain (u_dom0_app HG HR HOm HC f d' u H2 Hu) as v Hv. exact (u_dom0_in HG HR HOm HC f d u v H1 Hv).
Qed.

Lemma dom0_intro {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) f d :
  (forall G' u, incl G G' -> G' ⊢C u ∈' d -> G' ⊢C ∃ App0 f`[↑] u`[↑] $0) ->
  (forall G' u v, incl G G' -> G' ⊢C App0 f u v -> G' ⊢C u ∈' d) -> G ⊢C Dom0 f d.
Proof.
  intros H1 H2. pose proof (incl_refl G) as Hs. unfold Dom0. fsplit.
  - fall u. fintro Hu. fhave Hv : (H1 _ u Hs Hu). fex Hv v Hv1. unfold App0 in Hv1. fex Hv1 p Hp. fdestr Hp Hp1 Hp2.
    fhave Hc2 : (op0_c2 HG u v p Hp2). fex Hc2 s Hs'. fdestr Hs' Hs1 Hs2.
    fexists p. fsplit; [exact Hp1|]. fexists s. fsplit; [exact Hs1|]. fexists v. fsplit; [exact Hs2|exact Hp2].
  - apply (u_pairsall_intro HG HR HOm HC). intros G' u v HGG' Huv. simp. exact (H2 G' u v (incl_tran Hs HGG') Huv).
Qed.

Lemma fb_S_dom : fb 2 S_dom. Proof. fbcomp. Qed.

Lemma dom_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) e : G ⊢C ∃ Dom0 e`[↑] $0.
Proof.
  fobtain (union_ex HG e) as u1 Hu1. fobtain (union_ex HG u1) as u2 Hu2.
  pose proof (sep_use _ 1 S_dom (fun _ => e) u2 (in_S_dom _ HC) fb_S_dom) as Hd. fex Hd d Hd1. rename Hd1 into Hd.
  fexists d. pose proof (incl_refl Γ) as Hs. apply (dom0_intro HG HR HOm HC).
  - intros G' u HGG' Hu. wk HGG'. finst Hd u. exact (CE2 (iff_l _ _ _ Hd Hu)).
  - intros G' u v HGG' Huv. wk HGG'. finst Hd u. apply (iff_r _ _ _ Hd). fsplit; [|fexists v; exact Huv].
    unfold App0 in Huv. fex Huv p Hp. fdestr Hp Hp1 Hp2.
    fhave Hc1 : (op0_c1 HG u v p Hp2). fex Hc1 s Hs'. fdestr Hs' Hs1 Hs2.
    apply (union_in HG u1 u2 s u Hu2); [|exact Hs2]. exact (union_in HG e u1 p s Hu1 Hp1 Hs1).
Qed.

Lemma ext0_char {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) e v z d p : G ⊢C Ext0 e v z -> G ⊢C Dom0 e d -> G ⊢C OP0 d v p -> G ⊢C Adj e p z.
Proof.
  intros H Hd Hp. unfold Ext0 in H. fex H p' Hp'. fdestr Hp' Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2.
  fex Hs2 d' Hd'. fdestr Hd' Hd1 Hd2. fdestr Hd2 Hd3 Hsub. fdestr Hd3 Hd4 Hall. fdestr Hd4 Hop Hdom.
  fhave E1 : (dom0_unique HG HR HOm HC e d' d Hdom Hd).
  frew_in E1 (OP0 $0 v`[↑] p'`[↑]) Hop.
  fhave E2 : (u_op0_unique HG HR HOm HC d v p' p Hop Hp).
  unfold Adj. fall q. fsplit.
  - fintro Hq. finst Hall q. fmp Hall Hq. fcases Hall A1 A2; [fleft; exact A1 | fright; feq].
  - fintro Hq. fcases Hq A1 A2; [exact (sub0_use HG e z q Hsub A1) | fmem].
Qed.

Lemma ext0_intro {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) e v z d p : G ⊢C Dom0 e d -> G ⊢C OP0 d v p -> G ⊢C Adj e p z -> G ⊢C Ext0 e v z.
Proof.
  intros Hd Hp Hz. fhave Hc1 : (op0_c1 HG d v p Hp). fex Hc1 s Hs. fdestr Hs Hs1 Hs2.
  unfold Ext0. fexists p. fsplit; [exact (adj_in_r HG e p z Hz)|]. fexists s. fsplit; [exact Hs1|].
  fexists d. fsplit; [exact Hs2|]. fsplit; [fsplit; [fsplit; [exact Hp|exact Hd]|]|].
  - fall q. fintro Hq. exact (adj_el HG e p z q Hz Hq).
  - unfold Sub0. fall q. fintro Hq. exact (adj_in_l HG e p z q Hz Hq).
Qed.

Lemma ext0_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) e v : G ⊢C ∃ Ext0 e`[↑] v`[↑] $0.
Proof.
  fobtain (dom_ex HG HR HOm HC e) as d Hd. fobtain (u_op0_ex HG HR HOm HC d v) as p Hp.
  fobtain (adj_ex HG e p) as z Hz. fexists z. exact (ext0_intro HG HR HOm HC e v z d p Hd Hp Hz).
Qed.

Lemma ext0_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) e v z z' : G ⊢C Ext0 e v z -> G ⊢C Ext0 e v z' -> G ⊢C z ≡' z'.
Proof.
  intros H1 H2. fobtain (dom_ex HG HR HOm HC e) as d Hd. fobtain (u_op0_ex HG HR HOm HC d v) as p Hp.
  exact (adj_unique HG e p z z' (ext0_char HG HR HOm HC e v z d p H1 Hd Hp)
                                (ext0_char HG HR HOm HC e v z' d p H2 Hd Hp)).
Qed.

(** ** Unions of images (one replacement instance [UF F]) *)
Lemma UF_inst F a b sg : (UF F)[a .: b .: sg] = ∀ ($0 ∈' b`[↑] ↔ F[$0 .: a`[↑] .: (fun k => (sg k)`[↑])]).
Proof.
  unfold UF. cbn. rewrite !subst_comp.
  erewrite (subst_ext F); [reflexivity|]. intros [|[|k]]; reflexivity.
Qed.

Local Ltac feqs := repeat match goal with
  | |- ?x = ?x => reflexivity
  | |- ?F[?s] = ?F[?t] => apply subst_ext; let k := fresh "k" in intros [|[|k]]; term_eq
  | |- quant _ _ = quant _ _ => f_equal
  | |- bin _ _ _ = bin _ _ _ => f_equal
  end.
Local Ltac Fconv H := match type of H with _ ⊢C ?h => match goal with |- _ ⊢C ?g =>
  replace g with h; [exact H | rewrite ?subst_comp; feqs] end end.

Lemma uimg {G} (HG : incl ZF0base G) n F sg X : In (forall_times n (ax_rep' (UF F))) G -> fb (S (S n)) F ->
  (forall G' x, incl G G' -> G' ⊢C ∃ ∀ ($0 ∈' $1 ↔ F[$0 .: x`[↑]`[↑] .: (fun k => (sg k)`[↑]`[↑])])) ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' X`[↑]`[↑]`[↑] ∧ F[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])])).
Proof.
  intros Hin Hfb Hex. pose proof (incl_refl G) as Hs.
  assert (HfbU : fb (S (S n)) (UF F)).
  { unfold UF. cbn. repeat split; try lia; eapply fb_subst; try exact Hfb; intros [|[|i]] Hi; cbn; lia. }
  assert (Hfun : forall a b b', G ⊢C (UF F)[a .: b .: sg] → (UF F)[a .: b' .: sg] → b ≡' b').
  { intros a b b'. rewrite !UF_inst. apply II, II.
    eapply (ext_char (incl_cons_r _ _ _ (incl_cons_r _ _ _ HG))); apply Ctx; [right|]; now left. }
  pose proof (rep_use G n (UF F) sg X Hin HfbU Hfun) as HW. rewrite UF_inst in HW.
  fex HW W HW1. rename HW1 into HW. fobtain (union_ex HG W) as U HU.
  fexists U. fall z. fsplit.
  - fintro Hz. fhave H : (union_el HG W U z HU Hz). fex H Y HY. fdestr HY HY1 HY2.
    finst HW Y. fhave H : (iff_l _ _ _ HW HY1). fex H x Hx. fdestr Hx Hx1 Hx2.
    finst Hx2 z. fhave Hf : (iff_l _ _ _ Hx2 HY2).
    fexists x. fsplit; [exact Hx1|]. Fconv Hf.
  - fintro Hz. fex Hz x Hx. fdestr Hx Hx1 Hf.
    fobtain (Hex _ x Hs) as Y HY. finst HW Y. apply (union_in HG W U Y z HU).
    + apply (iff_r _ _ _ HW). fexists x. fsplit; [exact Hx1|]. Fconv HY.
    + finst HY z. apply (iff_r _ _ _ HY). Fconv Hf.
Qed.

Local Ltac uF := unfold F_ext, F_op3, F_s1, F_s2, F_s3 in *.

(** ** Existence and uniqueness of the operations *)
Lemma fb_S_neg : fb 2 S_neg. Proof. fbcomp. Qed.
Lemma fb_S_pj : fb 3 S_pj. Proof. fbcomp. Qed.
Lemma fb_S_sc : fb 3 S_sc. Proof. fbcomp. Qed.
Lemma fb_S_ai : fb 3 S_ai. Proof. fbcomp. Qed.
Lemma fb_S_ae : fb 3 S_ae. Proof. fbcomp. Qed.
Lemma fb_F_ext : fb 3 F_ext. Proof. fbcomp. Qed.
Lemma fb_F_op3 : fb 3 F_op3. Proof. fbcomp. Qed.
Lemma fb_F_s1 : fb 4 F_s1. Proof. fbcomp. Qed.
Lemma fb_F_s2 : fb 4 F_s2. Proof. fbcomp. Qed.
Lemma fb_F_s3 : fb 3 F_s3. Proof. fbcomp. Qed.

Lemma pair0_unique {G} (HG : incl ZF0base G) a b y y' : G ⊢C Pair0 a b y -> G ⊢C Pair0 a b y' -> G ⊢C y ≡' y'.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
  - fhave E : (pair0_el HG a b y z H1 Hz). fhave Ha : (pair0_l HG a b y' H2). fhave Hb : (pair0_r HG a b y' H2).
    fcases E E1 E2; fmem.
  - fhave E : (pair0_el HG a b y' z H2 Hz). fhave Ha : (pair0_l HG a b y H1). fhave Hb : (pair0_r HG a b y H1).
    fcases E E1 E2; fmem.
Qed.

Lemma sepof_unique {G} (HG : incl ZF0base G) a y y' P : G ⊢C SepOf a y P -> G ⊢C SepOf a y' P -> G ⊢C y ≡' y'.
Proof. intros H1 H2. exact (ext_char HG _ y y' (sepof_iff HG a y P H1) (sepof_iff HG a y' P H2)). Qed.

Lemma op3_sub {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) a b c y y' :
  G ⊢C Op 3 a b c y -> G ⊢C Op 3 a b c y' -> G ⊢C sub' y y'.
Proof.
  intros H1 H2. cbv beta iota delta [Op] in H1, H2. pose proof (CE1 H1) as A1. pose proof (CE2 H2) as B2.
  clear H1 H2. unfold sub'. fall z. fintro Hz. finst A1 z. fmp A1 Hz. fex A1 e He. fdestr He He1 He2.
  fex He2 v Hv. fdestr Hv Hv1 Hv2. finst B2 e. fmp B2 He1. finst B2 v. fmp B2 Hv1. fex B2 z' Hz'.
  fdestr Hz' Hz1 Hz2. fhave E : (ext0_unique HG HR HOm HC e v z z' Hv2 Hz2). fmem.
Qed.

Lemma op_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) k a b c y y' :
  k < 8 -> G ⊢C Op k a b c y -> G ⊢C Op k a b c y' -> G ⊢C y ≡' y'.
Proof.
  intros Hk H1 H2. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia.
  - exact (pair0_unique HG a b y y' H1 H2).
  - exact (u_union0_unique HG HR HOm HC a y y' H1 H2).
  - exact (sepof_unique HG a y y' _ H1 H2).
  - exact (ext_rule HG y y' (op3_sub HG HR HOm HC a b c y y' H1 H2) (op3_sub HG HR HOm HC a b c y' y H2 H1)).
  - exact (sepof_unique HG a y y' _ H1 H2).
  - exact (sepof_unique HG c y y' _ H1 H2).
  - exact (sepof_unique HG a y y' _ H1 H2).
  - exact (sepof_unique HG a y y' _ H1 H2).
Qed.

Lemma op3_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) a b c :
  G ⊢C ∃ Op 3 a`[↑] b`[↑] c`[↑] $0.
Proof.
  assert (Hin : forall G' e, incl G G' ->
    G' ⊢C ∃ ∀ ($0 ∈' $1 ↔ F_op3[$0 .: e`[↑]`[↑] .: (fun k => ((fun _ => b) k)`[↑]`[↑])])).
  { intros G' e HGG'. wk HGG'.
    assert (Hin2 : forall G'' v, incl G' G'' ->
      G'' ⊢C ∃ ∀ ($0 ∈' $1 ↔ F_ext[$0 .: v`[↑]`[↑] .: (fun k => ((fun _ => e) k)`[↑]`[↑])])).
    { intros G'' v H2. wk H2. uF. simp.
      fobtain (ext0_ex HG HR HOm HC e v) as z0 Hz0. fobtain (sing_ex HG z0) as s Hs0.
      fexists s. fall z. fsplit.
      - fintro Hz. fhave E : (sing_el HG z0 s z Hs0 Hz). frew_in E (Ext0 e`[↑] v`[↑] $0) Hz0. exact Hz0.
      - fintro Hz. fhave E : (ext0_unique HG HR HOm HC e v z z0 Hz Hz0). exact (sing_in' HG z0 s z Hs0 E). }
    pose proof (uimg HG 1 F_ext (fun _ => e) b (in_F_ext _ HC) fb_F_ext Hin2) as H. uF. simp_in H. simp. exact H. }
  pose proof (uimg HG 1 F_op3 (fun _ => b) a (in_F_op3 _ HC) fb_F_op3 Hin) as H. uF. simp_in H.
  fex H U HU. fexists U. cbv beta iota delta [Op]. fsplit.
  - fall y. fintro Hy. finst HU y. exact (iff_l _ _ _ HU Hy).
  - fall e. fintro He. fall v. fintro Hv. fobtain (ext0_ex HG HR HOm HC e v) as z Hz. fexists z. fsplit; [|exact Hz].
    finst HU z. apply (iff_r _ _ _ HU). fexists e. fsplit; [exact He|]. fexists v. fsplit; [exact Hv | exact Hz].
Qed.

Lemma op_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) k a b c :
  k < 8 -> G ⊢C ∃ Op k a`[↑] b`[↑] c`[↑] $0.
Proof.
  intros Hk. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia.
  - exact (u_pair0_ex HG HR HOm HC a b).
  - exact (u_union0_ex HG HR HOm HC a).
  - fobtain (sep_use _ 1 S_neg (fun _ => b) a (in_S_neg _ HC) fb_S_neg) as y Hy.
    fexists y. apply (sepof_intro HG). unfold S_neg, S_pj, S_sc, S_ai, S_ae in Hy. simp_in Hy. exact Hy.
  - exact (op3_ex HG HR HOm HC a b c).
  - fobtain (sep_use _ 2 S_pj (b .: (fun _ => c)) a (in_S_pj _ HC) fb_S_pj) as y Hy.
    fexists y. apply (sepof_intro HG). unfold S_neg, S_pj, S_sc, S_ai, S_ae in Hy. simp_in Hy. exact Hy.
  - fobtain (sep_use _ 2 S_sc (a .: (fun _ => b)) c (in_S_sc _ HC) fb_S_sc) as y Hy.
    fexists y. apply (sepof_intro HG). unfold S_neg, S_pj, S_sc, S_ai, S_ae in Hy. simp_in Hy. exact Hy.
  - fobtain (sep_use _ 2 S_ai (b .: (fun _ => c)) a (in_S_ai _ HC) fb_S_ai) as y Hy.
    fexists y. apply (sepof_intro HG). unfold S_neg, S_pj, S_sc, S_ai, S_ae in Hy. simp_in Hy. exact Hy.
  - fobtain (sep_use _ 2 S_ae (b .: (fun _ => c)) a (in_S_ae _ HC) fb_S_ae) as y Hy.
    fexists y. apply (sepof_intro HG). unfold S_neg, S_pj, S_sc, S_ai, S_ae in Hy. simp_in Hy. exact Hy.
Qed.

(** the set {op_0(a,b,c), ..., op_k(a,b,c)} *)
Lemma opsup_set_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) k a b c :
  k < 8 -> G ⊢C ∃ ∀ ($0 ∈' $1 ↔ OpsUp k a`[↑]`[↑] b`[↑]`[↑] c`[↑]`[↑] $0).
Proof.
  induction k as [|k IH]; intros Hk.
  - fobtain (op_ex HG HR HOm HC 0 a b c ltac:(lia)) as o Ho. fobtain (sing_ex HG o) as s Hs.
    fexists s. fall z. fsplit.
    + fintro Hz. fhave E : (sing_el HG o s z Hs Hz). frew_in E (Op 0 a`[↑] b`[↑] c`[↑] $0) Ho. exact Ho.
    + fintro Hz. fhave E : (op_unique HG HR HOm HC 0 a b c z o ltac:(lia) Hz Ho). exact (sing_in' HG o s z Hs E).
  - fhave H : (IH ltac:(lia)). fex H S0 HS. fobtain (op_ex HG HR HOm HC (S k) a b c Hk) as o Ho.
    fobtain (adj_ex HG S0 o) as s Hs. fexists s. fall z. finst HS z. fsplit.
    + fintro Hz. fhave E : (adj_el HG S0 o s z Hs Hz). fcases E E1 E2.
      * fleft. exact (iff_l _ _ _ HS E1).
      * fright. frew_in E2 (Op (S k) a`[↑] b`[↑] c`[↑] $0) Ho. exact Ho.
    + fintro Hz. apply (adj_in HG S0 o s z Hs). fcases Hz E1 E2.
      * fleft. exact (iff_r _ _ _ HS E1).
      * fright. exact (op_unique HG HR HOm HC (S k) a b c z o Hk E2 Ho).
Qed.

Lemma ops_set_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) a b c :
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ Ops a`[↑]`[↑] b`[↑]`[↑] c`[↑]`[↑] $0).
Proof. exact (opsup_set_ex HG HR HOm HC 7 a b c ltac:(lia)). Qed.

(** ** Step *)
Lemma step_ex_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) X :
  G ⊢C ∃ Step X`[↑] $0.
Proof.
  assert (L1 : forall G' a b, incl G G' ->
    G' ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' X`[↑]`[↑]`[↑] ∧ Ops a`[↑]`[↑]`[↑] b`[↑]`[↑]`[↑] $0 $1))).
  { intros G' a b HGG'. wk HGG'.
    assert (Hex : forall G'' x, incl G' G'' ->
      G'' ⊢C ∃ ∀ ($0 ∈' $1 ↔ F_s1[$0 .: x`[↑]`[↑] .: (fun k => ((a .: (fun _ => b)) k)`[↑]`[↑])])).
    { intros G'' c H2. wk H2. uF. simp. exact (ops_set_ex HG HR HOm HC a b c). }
    pose proof (uimg HG 2 F_s1 (a .: (fun _ => b)) X (in_F_s1 _ HC) fb_F_s1 Hex) as H. uF. simp_in H. exact H. }
  assert (L2 : forall G' a, incl G G' ->
    G' ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' X`[↑]`[↑]`[↑] ∧ ∃ ($0 ∈' X`[↑]`[↑]`[↑]`[↑] ∧ Ops a`[↑]`[↑]`[↑]`[↑] $1 $0 $2)))).
  { intros G' a HGG'.
    assert (Hex : forall G'' x, incl G' G'' ->
      G'' ⊢C ∃ ∀ ($0 ∈' $1 ↔ F_s2[$0 .: x`[↑]`[↑] .: (fun k => ((a .: (fun _ => X)) k)`[↑]`[↑])])).
    { intros G'' b H2. uF. simp. exact (L1 G'' a b (incl_tran HGG' H2)). }
    wk HGG'.
    pose proof (uimg HG 2 F_s2 (a .: (fun _ => X)) X (in_F_s2 _ HC) fb_F_s2 Hex) as H. uF. simp_in H. exact H. }
  assert (Hex : forall G' x, incl G G' ->
      G' ⊢C ∃ ∀ ($0 ∈' $1 ↔ F_s3[$0 .: x`[↑]`[↑] .: (fun k => ((fun _ => X) k)`[↑]`[↑])])).
  { intros G' a H2. uF. simp. exact (L2 G' a H2). }
  pose proof (uimg HG 1 F_s3 (fun _ => X) X (in_F_s3 _ HC) fb_F_s3 Hex) as HU. uF. simp_in HU.
  fex HU U HU1. rename HU1 into HU.
  fobtain (bun_ex HG X U) as Y HY. fexists Y. unfold Step. fsplit; [fsplit|].
  - unfold Sub0. fall z. fintro Hz. apply (bun_in HG X U Y z HY). fleft. exact Hz.
  - fall z. fintro Hz. fhave H : (bun_el HG X U Y z HY Hz). fcases H H1 H2; [fleft; exact H1|fright].
    finst HU z. exact (iff_l _ _ _ HU H2).
  - fall a. fintro Ha. fall b. fintro Hb. fall c. fintro Hc. apply opsin_intro. intros k Hk.
    fobtain (op_ex HG HR HOm HC k a b c Hk) as o Ho. fexists o. fsplit; [|exact Ho].
    apply (bun_in HG X U Y o HY). fright. finst HU o. apply (iff_r _ _ _ HU).
    fexists a. fsplit; [exact Ha|]. fexists b. fsplit; [exact Hb|]. fexists c. fsplit; [exact Hc|].
    exact (ops_inj k a b c o Hk Ho).
Qed.

Lemma step_sub {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) X Y Y' :
  G ⊢C Step X Y -> G ⊢C Step X Y' -> G ⊢C sub' Y Y'.
Proof.
  intros H1 H2. unfold Step in H1, H2. fdestr H1 H1a H1c. fdestr H1a H1s H1b. fdestr H2 H2a H2c. fdestr H2a H2s H2b.
  unfold sub'. fall z. fintro Hz. finst H1b z. fmp H1b Hz. fcases H1b A B.
  - exact (sub0_use HG X Y' z H2s A).
  - fex B a Ha. fdestr Ha Ha1 Ha2. fex Ha2 b Hb. fdestr Hb Hb1 Hb2. fex Hb2 c Hc. fdestr Hc Hc1 Hc2.
    finst H2c a. fmp H2c Ha1. finst H2c b. fmp H2c Hb1. finst H2c c. fmp H2c Hc1.
    eapply IE; [|exact Hc2]. apply ops_elim. intros k Hk. fintro Hop.
    fhave H : (opsin_proj k Y' a b c Hk H2c). fex H y Hy. fdestr Hy Hy1 Hy2.
    fhave E : (op_unique HG HR HOm HC k a b c z y Hk Hop Hy2). fmem.
Qed.

Lemma step_unique_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) X Y Y' :
  G ⊢C Step X Y -> G ⊢C Step X Y' -> G ⊢C Y ≡' Y'.
Proof.
  intros H1 H2. exact (ext_rule HG Y Y' (step_sub HG HR HOm HC X Y Y' H1 H2) (step_sub HG HR HOm HC X Y' Y H2 H1)).
Qed.


(** ** The recursion step Scl *)
Definition SclF (f xi v B : term) : form :=
  (Emp0 xi → v ≡' B) ∧ (∀ ($0 ∈' xi`[↑] → Succ0 $0 xi`[↑] → ∃ (App0 f`[↑]`[↑] $1 $0 ∧ Step $0 v`[↑]`[↑]))) ∧
  (Lim0 xi → Emp0 v).
Lemma SR_Scl f xi v B : SR Scl f xi v B = SclF f xi v B.
Proof. unfold SR, Scl, SclF. cbn. autorewrite with fsub. cbn. reflexivity. Qed.

Section Ordh.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).

Lemma lim_nonemp l : G ⊢C Lim0 l -> G ⊢C Emp0 l -> G ⊢C ⊥.
Proof.
  intros H He. unfold Lim0 in H. pose proof (CE2 (CE1 H)) as H1. fex H1 y Hy.
  exact (emp0_el HG l y He (CE1 Hy)).
Qed.
Lemma succ_nonemp a s : G ⊢C Succ0 a s -> G ⊢C Emp0 s -> G ⊢C ⊥.
Proof. intros H He. exact (emp0_el HG s a He (succ0_self HG a s H)). Qed.
Lemma succ_nolim a s : G ⊢C Succ0 a s -> G ⊢C Lim0 s -> G ⊢C ⊥.
Proof.
  intros H Hl. unfold Lim0 in Hl. pose proof (CE2 Hl) as H2. finst H2 a. fmp H2 (succ0_self HG a s H).
  fex H2 c Hc. fdestr Hc Hc1 Hc2. fhave E : (succ0_el HG a s c H Hc1). fcases E E1 E2.
  - exact (u_no_cycle2 HG HR HOm HC a c Hc2 E1).
  - apply (u_no_self HG HR HOm HC a). fmem.
Qed.
Lemma succ_inj a a' s : G ⊢C Succ0 a s -> G ⊢C Succ0 a' s -> G ⊢C a ≡' a'.
Proof.
  intros H H'. fhave E1 : (succ0_el HG a' s a H' (succ0_self HG a s H)).
  fhave E2 : (succ0_el HG a s a' H (succ0_self HG a' s H')).
  fcases E1 A1 A2; [|exact A2]. fcases E2 B1 B2; [|feq].
  fabsurd. exact (u_no_cycle2 HG HR HOm HC a a' A1 B1).
Qed.
Lemma sub0_trans x y z : G ⊢C Sub0 x y -> G ⊢C Sub0 y z -> G ⊢C Sub0 x z.
Proof. intros H1 H2. unfold Sub0. fall u. fintro Hu. exact (sub0_use HG y z u H2 (sub0_use HG x y u H1 Hu)). Qed.
Lemma sub0_refl x : G ⊢C Sub0 x x.
Proof. unfold Sub0. fall u. fintro Hu. exact Hu. Qed.
Lemma step_sub0 X Y : G ⊢C Step X Y -> G ⊢C Sub0 X Y.
Proof. intros H. unfold Step in H. exact (CE1 (CE1 H)). Qed.
End Ordh.

Lemma Scl_loc_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B :
  G ⊢C SLoc Scl B.
Proof.
  unfold SLoc. fall f. fall f'. fall xi. fall v. fintro Hf. fintro Hf'. fintro Hxi. fintro Ha. fintro H.
  rewrite SR_Scl in H |- *. unfold SclF in H |- *. fdestr H H12 H3. fdestr H12 H1 H2.
  fsplit; [fsplit; [exact H1|]|exact H3].
  fall e. fintro He. fintro Hs. finst H2 e. fmp H2 He. fmp H2 Hs. fex H2 w Hw. fdestr Hw Hw1 Hw2.
  fexists w. fsplit; [|exact Hw2]. unfold Agree in Ha. finst Ha e. fmp Ha He. finst Ha w. exact (iff_l _ _ _ Ha Hw1).
Qed.

Lemma Scl_tot_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B :
  G ⊢C STot Scl B.
Proof.
  unfold STot. fall f. fall xi. fintro Hf. fintro Hxi. fintro Hall.
  fhave Hc : (u_ord_cases HG HR HOm HC xi Hxi). fcases Hc C0 C3; [fcases C0 C1 C2|].
  - fexists B. rewrite SR_Scl. unfold SclF. fsplit; [fsplit|].
    + fintro He. feq.
    + fall e. fintro He. fabsurd. exact (emp0_el HG xi e C1 He).
    + fintro Hl. fabsurd. exact (lim_nonemp HG HR HOm HC xi Hl C1).
  - fex C2 a Ha. fdestr Ha Ha1 Ha2. finst Hall a. fmp Hall (succ0_self HG a xi Ha2). fex Hall w Hw.
    fobtain (step_ex_g HG HR HOm HC w) as v Hv. fexists v. rewrite SR_Scl. unfold SclF. fsplit; [fsplit|].
    + fintro He. fabsurd. exact (succ_nonemp HG HR HOm HC a xi Ha2 He).
    + fall e. fintro He. fintro Hs. fhave E : (succ_inj HG HR HOm HC a e xi Ha2 Hs).
      fexists w. fsplit; [|exact Hv]. frew_in E (App0 f`[↑] $0 w`[↑]) Hw. exact Hw.
    + fintro Hl. fabsurd. exact (succ_nolim HG HR HOm HC a xi Ha2 Hl).
  - fobtain (u_emp0_ex HG HR HOm HC) as v Hv. fexists v. rewrite SR_Scl. unfold SclF. fsplit; [fsplit|].
    + fintro He. fabsurd. exact (lim_nonemp HG HR HOm HC xi C3 He).
    + fall e. fintro He. fintro Hs. fabsurd. exact (succ_nolim HG HR HOm HC e xi Hs C3).
    + fintro Hl. exact Hv.
Qed.

Lemma Scl_fun_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B :
  G ⊢C SFun Scl B.
Proof.
  unfold SFun. fall f. fall xi. fall v. fall v'. fintro Hf. fintro Hxi. fintro H. fintro H'.
  rewrite SR_Scl in H, H'. unfold SclF in H, H'. fdestr H H12 H3. fdestr H12 H1 H2. fdestr H' H12' H3'. fdestr H12' H1' H2'.
  fhave Hc : (u_ord_cases HG HR HOm HC xi Hxi). fcases Hc C0 C3; [fcases C0 C1 C2|].
  - fmp H1 C1. fmp H1' C1. feq.
  - fex C2 a Ha. fdestr Ha Ha1 Ha2. finst H2 a. fmp H2 (succ0_self HG a xi Ha2). fmp H2 Ha2.
    finst H2' a. fmp H2' (succ0_self HG a xi Ha2). fmp H2' Ha2.
    fex H2 w Hw. fdestr Hw Hw1 Hw2. fex H2' w' Hw'. fdestr Hw' Hw1' Hw2'.
    fhave E : (u_fun0_app HG HR HOm HC f a w w' Hf Hw1 Hw1'). frew_in E (Step $0 v'`[↑]) Hw2'.
    exact (step_unique_g HG HR HOm HC w v v' Hw2 Hw2').
  - fmp H3 C3. fmp H3' C3. exact (u_emp0_unique HG HR HOm HC v v' H3 H3').
Qed.

Lemma u_rec_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B d :
  G ⊢C Ord0 d -> G ⊢C ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK Scl B`[↑] $0).
Proof.
  intros Hd. pre. pose proof (Ax_cl_rec _ HC) as HI.
  eapply rec_ex; first [ eassumption | exact fb_Scl | exact (Scl_loc_g HG HR HOm HC B)
                       | exact (Scl_tot_g HG HR HOm HC B) | exact (Scl_fun_g HG HR HOm HC B) ].
Qed.

Lemma u_rec_agree {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G)
  B d d' f f' xi u u' :
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK Scl B f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK Scl B f' ->
  G ⊢C xi ∈' d -> G ⊢C xi ∈' d' -> G ⊢C App0 f xi u -> G ⊢C App0 f' xi u' -> G ⊢C u ≡' u'.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. pre. pose proof (Ax_cl_rec _ HC) as HI.
  first [ exact (rec_agree HG HR HO Scl fb_Scl HI B d d' f f' xi u u' (Scl_loc_g HG HR HOm HC B)
                  (Scl_fun_g HG HR HOm HC B) H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
        | eapply rec_agree; first [ eassumption | exact fb_Scl | exact (Scl_loc_g HG HR HOm HC B)
                                  | exact (Scl_fun_g HG HR HOm HC B) ] ].
Qed.

(** ** ⋃ ran g *)
Section Ran.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).

Lemma ran_el g C x : G ⊢C RanU g C -> G ⊢C x ∈' C -> G ⊢C ∃ ∃ (App0 g`[↑]`[↑] $1 $0 ∧ x`[↑]`[↑] ∈' $0).
Proof.
  intros H Hx. unfold RanU in H. pose proof (CE1 H) as H1. finst H1 x. fmp H1 Hx.
  fex H1 p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2. fex Hs2 t Ht. fdestr Ht Ht1 Ht2.
  fdestr Ht2 Hxt Hu. fex Hu s' Hs'. fdestr Hs' Hs'1 Hs'2. fex Hs'2 u Hu. fdestr Hu Hu1 Hu2.
  fexists u. fexists t. fsplit; [|exact Hxt]. exact (u_app0_intro HG HR HOm HC g u t p Hu2 Hp1).
Qed.
Lemma ran_sub g C u t : G ⊢C RanU g C -> G ⊢C App0 g u t -> G ⊢C Sub0 t C.
Proof.
  intros H Hut. unfold RanU in H. pose proof (CE2 H) as H2.
  pose proof (u_pairsall_use HG HR HOm HC g _ u t H2 Hut) as H3. simp_in H3. exact H3.
Qed.
End Ran.

Lemma fb_S_ran : fb 2 S_ran. Proof. fbcomp. Qed.
Lemma fb_S_mono : fb 2 S_mono. Proof. fbcomp. Qed.
Lemma fb_S_sub : fb 2 S_sub. Proof. fbcomp. Qed.

Lemma cl_ex_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B :
  G ⊢C ∃ Cl B`[↑] $0.
Proof.
  fobtain (u_om_ex HG HR HOm HC) as w Hw. fhave Hwo : (u_om_ord HG HR HOm HC w Hw).
  fobtain (u_rec_ex HG HR HOm HC B w Hwo) as g Hg. fdestr Hg Hg12 Hg3. fdestr Hg12 Hg1 Hg2.
  fobtain (union_ex HG g) as u1 Hu1. fobtain (union_ex HG u1) as u2 Hu2. fobtain (union_ex HG u2) as u3 Hu3.
  pose proof (sep_use _ 1 S_ran (fun _ => g) u3 (in_S_ran _ HC) fb_S_ran) as T. unfold S_ran in T. simp_in T.
  fex T C HCC. fexists C. unfold Cl. fexists w. fexists g.
  fsplit; [fsplit; [fsplit; [fsplit; [exact Hw|exact Hg1]|exact Hg2]|exact Hg3]|]. unfold RanU. fsplit.
  - fall x. fintro Hx. finst HCC x. fhave H : (CE2 (iff_l _ _ _ HCC Hx)). fex H u Hu. fex Hu t Ht. fdestr Ht Ht1 Ht2.
    unfold App0 in Ht1. fex Ht1 p Hp. fdestr Hp Hp1 Hp2.
    fhave Hc2 : (op0_c2 HG u t p Hp2). fex Hc2 s Hs. fdestr Hs Hs1 Hs2.
    fhave Hc1 : (op0_c1 HG u t p Hp2). fex Hc1 s' Hs'. fdestr Hs' Hs'1 Hs'2.
    fexists p. fsplit; [exact Hp1|]. fexists s. fsplit; [exact Hs1|]. fexists t. fsplit; [exact Hs2|].
    fsplit; [exact Ht2|]. fexists s'. fsplit; [exact Hs'1|]. fexists u. fsplit; [exact Hs'2|exact Hp2].
  - apply (u_pairsall_intro HG HR HOm HC). intros G' u t HGG' Hut. wk HGG'. simp.
    unfold Sub0. fall x. fintro Hx. finst HCC x. apply (iff_r _ _ _ HCC). fsplit.
    + pose proof Hut as Hut'. unfold App0 in Hut'. fex Hut' p Hp. fdestr Hp Hp1 Hp2.
      fhave Hc2 : (op0_c2 HG u t p Hp2). fex Hc2 s Hs. fdestr Hs Hs1 Hs2.
      apply (union_in HG u2 u3 t x Hu3); [|exact Hx]. apply (union_in HG u1 u2 s t Hu2); [|exact Hs2].
      exact (union_in HG g u1 p s Hu1 Hp1 Hs1).
    + fexists u. fexists t. fsplit; [exact Hut|exact Hx].
Qed.

(** unpacking Cl *)
Lemma cl_unpack {G} (HG : incl ZF0base G) B C psi : G ⊢C Cl B C ->
  (forall G' w g, incl G G' -> G' ⊢C Om0 w -> G' ⊢C Fun0 g -> G' ⊢C Dom0 g w -> G' ⊢C RecOK Scl B g ->
     G' ⊢C RanU g C -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  intros H K. pose proof (incl_refl G) as Hs. unfold Cl in H. fex H w Hw. fex Hw g Hg.
  fdestr Hg Ha Hg5. fdestr Ha Hb Hg4. fdestr Hb Hc Hg3. fdestr Hc Hg1 Hg2.
  exact (K _ w g Hs Hg1 Hg2 Hg3 Hg4 Hg5).
Qed.

Lemma cl_unique_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B C C' :
  G ⊢C Cl B C -> G ⊢C Cl B C' -> G ⊢C sub' C C'.
Proof.
  intros H H'. apply (cl_unpack HG B C _ H). intros G1 w g H1 Hw Hf Hd Hr Hu. wk H1.
  apply (cl_unpack HG B C' _ H'). intros G2 w' g' H2 Hw' Hf' Hd' Hr' Hu'. wk H2.
  unfold sub'. fall x. fintro Hx. fhave H3 : (ran_el HG HR HOm HC g C x Hu Hx). fex H3 u Hu1. fex Hu1 t Ht. fdestr Ht Ht1 Ht2.
  fhave Hud : (u_dom0_in HG HR HOm HC g w u t Hd Ht1). fhave E : (u_om_unique HG HR HOm HC w w' Hw Hw').
  fassert Hud' : (u ∈' w'). { fmem. }
  fobtain (u_dom0_app HG HR HOm HC g' w' u Hd' Hud') as t' Ht'.
  fhave E2 : (u_rec_agree HG HR HOm HC B w w' g g' u t t' (u_om_ord HG HR HOm HC w Hw) Hf Hd Hr
               (u_om_ord HG HR HOm HC w' Hw') Hf' Hd' Hr' Hud Hud' Ht1 Ht').
  apply (sub0_use HG t' C' x (ran_sub HG HR HOm HC g' C' u t' Hu' Ht')). fmem.
Qed.

Lemma stage0 {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B g e t :
  G ⊢C RecOK Scl B g -> G ⊢C Emp0 e -> G ⊢C App0 g e t -> G ⊢C t ≡' B.
Proof.
  intros Hr He Ht. unfold RecOK in Hr. pose proof (u_pairsall_use HG HR HOm HC g _ e t Hr Ht) as H.
  simp_in H. rewrite SR_Scl in H. unfold SclF in H. exact (IE (CE1 (CE1 H)) He).
Qed.

Lemma stageS {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B g n s t :
  G ⊢C RecOK Scl B g -> G ⊢C Succ0 n s -> G ⊢C App0 g s t -> G ⊢C ∃ (App0 g`[↑] n`[↑] $0 ∧ Step $0 t`[↑]).
Proof.
  intros Hr Hs Ht. unfold RecOK in Hr. pose proof (u_pairsall_use HG HR HOm HC g _ s t Hr Ht) as H.
  simp_in H. rewrite SR_Scl in H. unfold SclF in H. pose proof (CE2 (CE1 H)) as H2.
  finst H2 n. fmp H2 (succ0_self HG n s Hs). fmp H2 Hs. exact H2.
Qed.

Lemma cl_base_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B C x :
  G ⊢C Cl B C -> G ⊢C x ∈' B -> G ⊢C x ∈' C.
Proof.
  intros H Hx. apply (cl_unpack HG B C _ H). intros G1 w g H1 Hw Hf Hd Hr Hu. wk H1.
  fobtain (u_emp0_ex HG HR HOm HC) as e He. fhave Hew : (u_om_emp HG HR HOm HC w e Hw He).
  fobtain (u_dom0_app HG HR HOm HC g w e Hd Hew) as t Ht.
  fhave E : (stage0 HG HR HOm HC B g e t Hr He Ht).
  apply (sub0_use HG t C x (ran_sub HG HR HOm HC g C e t Hu Ht)). fmem.
Qed.

(** monotonicity of the stages *)
Lemma cl_mono {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B w g :
  G ⊢C Om0 w -> G ⊢C Fun0 g -> G ⊢C Dom0 g w -> G ⊢C RecOK Scl B g -> G ⊢C ∀ ($0 ∈' w`[↑] → Mono $0 g`[↑]).
Proof.
  intros Hw Hf Hd Hr.
  pose proof (sep_use _ 1 S_mono (fun _ => g) w (in_S_mono _ HC) fb_S_mono) as T. unfold S_mono in T. simp_in T.
  fex T X HX. fassert Hsub : (Sub0 w X).
  { apply (u_om_ind HG HR HOm HC w X Hw).
    - fall e. fintro He. finst HX e. apply (iff_r _ _ _ HX). fsplit; [exact (u_om_emp HG HR HOm HC w e Hw He)|].
      unfold Mono. fall m. fintro Hm. fabsurd. exact (emp0_el HG e m He Hm).
    - fall n. fintro Hn. fintro HnX. fall s. fintro Hs. fhave Hsw : (u_om_succ HG HR HOm HC w n s Hw Hn Hs).
      pose proof HX as HXs. finst HXs s. apply (iff_r _ _ _ HXs). fsplit; [exact Hsw|]. finst HX n. fhave Hmn : (CE2 (iff_l _ _ _ HX HnX)).
      unfold Mono. fall m. fintro Hm. fall t. fall t'. fintro Ht. fintro Ht'.
      fhave H : (stageS HG HR HOm HC B g n s t' Hr Hs Ht'). fex H w0 Hw0. fdestr Hw0 Hw01 Hw02.
      fhave Hw0t' : (step_sub0 HG HR HOm HC w0 t' Hw02).
      fhave E : (succ0_el HG n s m Hs Hm). fcases E E1 E2.
      + unfold Mono in Hmn. finst Hmn m. fmp Hmn E1. finst Hmn t w0. fmp Hmn Ht. fmp Hmn Hw01.
        exact (sub0_trans HG HR HOm HC t w0 t' Hmn Hw0t').
      + frew_in E2 (App0 g`[↑] $0 t`[↑]) Ht. fhave E3 : (u_fun0_app HG HR HOm HC g n t w0 Hf Ht Hw01).
        frew E3 (Sub0 $0 t'`[↑]). exact Hw0t'. }
  fall n. fintro Hn. finst HX n. exact (CE2 (iff_l _ _ _ HX (sub0_use HG w X n Hsub Hn))).
Qed.

Lemma stage_max {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) B w g i j ti tj :
  G ⊢C Om0 w -> G ⊢C Fun0 g -> G ⊢C Dom0 g w -> G ⊢C RecOK Scl B g ->
  G ⊢C i ∈' w -> G ⊢C j ∈' w -> G ⊢C App0 g i ti -> G ⊢C App0 g j tj ->
  G ⊢C ∃ ($0 ∈' w`[↑] ∧ ∃ (App0 g`[↑]`[↑] $1 $0 ∧ Sub0 ti`[↑]`[↑] $0 ∧ Sub0 tj`[↑]`[↑] $0)).
Proof.
  intros Hw Hf Hd Hr Hi Hj Hti Htj. fhave Hm : (cl_mono HG HR HOm HC B w g Hw Hf Hd Hr).
  fhave Hwo : (u_om_ord HG HR HOm HC w Hw).
  fhave T : (u_ord_tri HG HR HOm HC i j (u_ord_el HG HR HOm HC w i Hwo Hi) (u_ord_el HG HR HOm HC w j Hwo Hj)).
  fcases T T0 T3; [fcases T0 T1 T2|].
  - fexists j. fsplit; [exact Hj|]. fexists tj. fsplit; [fsplit; [exact Htj|]|exact (sub0_refl HG HR HOm HC tj)].
    finst Hm j. fmp Hm Hj. unfold Mono in Hm. finst Hm i. fmp Hm T1. finst Hm ti tj. fmp Hm Hti. fmp Hm Htj. exact Hm.
  - fexists j. fsplit; [exact Hj|]. fexists tj. fsplit; [fsplit; [exact Htj|]|exact (sub0_refl HG HR HOm HC tj)].
    frew_in T2 (App0 g`[↑] $0 ti`[↑]) Hti. fhave E : (u_fun0_app HG HR HOm HC g j ti tj Hf Hti Htj).
    frew E (Sub0 $0 tj`[↑]). exact (sub0_refl HG HR HOm HC tj).
  - fexists i. fsplit; [exact Hi|]. fexists ti. fsplit; [fsplit; [exact Hti|exact (sub0_refl HG HR HOm HC ti)]|].
    finst Hm i. fmp Hm Hi. unfold Mono in Hm. finst Hm j. fmp Hm T3. finst Hm tj ti. fmp Hm Htj. fmp Hm Hti. exact Hm.
Qed.

Lemma cl_op_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) k B C a b c :
  k < 8 -> G ⊢C Cl B C -> G ⊢C a ∈' C -> G ⊢C b ∈' C -> G ⊢C c ∈' C ->
  G ⊢C ∃ ($0 ∈' C`[↑] ∧ Op k a`[↑] b`[↑] c`[↑] $0).
Proof.
  intros Hk H Ha Hb Hc. apply (cl_unpack HG B C _ H). intros G1 w g H1 Hw Hf Hd Hr Hu. wk H1.
  fhave T : (ran_el HG HR HOm HC g C a Hu Ha). fex T i Hi. fex Hi ta Hta. fdestr Hta Hta1 Hta2.
  fhave T : (ran_el HG HR HOm HC g C b Hu Hb). fex T j Hj. fex Hj tb Htb. fdestr Htb Htb1 Htb2.
  fhave T : (ran_el HG HR HOm HC g C c Hu Hc). fex T l Hl. fex Hl tc Htc. fdestr Htc Htc1 Htc2.
  fhave Hiw : (u_dom0_in HG HR HOm HC g w i ta Hd Hta1). fhave Hjw : (u_dom0_in HG HR HOm HC g w j tb Hd Htb1).
  fhave Hlw : (u_dom0_in HG HR HOm HC g w l tc Hd Htc1).
  fhave T : (stage_max HG HR HOm HC B w g i j ta tb Hw Hf Hd Hr Hiw Hjw Hta1 Htb1).
  fex T n Hn. fdestr Hn Hn1 Hn2. fex Hn2 tn Htn. fdestr Htn Htn0 Htn3. fdestr Htn0 Htn1 Htn2.
  fhave T : (stage_max HG HR HOm HC B w g n l tn tc Hw Hf Hd Hr Hn1 Hlw Htn1 Htc1).
  fex T m Hm. fdestr Hm Hm1 Hm2. fex Hm2 tm Htm. fdestr Htm Htm0 Htm3. fdestr Htm0 Htm1 Htm2.
  fobtain (u_succ0_ex HG HR HOm HC m) as s Hs. fhave Hsw : (u_om_succ HG HR HOm HC w m s Hw Hm1 Hs).
  fobtain (u_dom0_app HG HR HOm HC g w s Hd Hsw) as ts Hts.
  fhave T : (stageS HG HR HOm HC B g m s ts Hr Hs Hts). fex T w0 Hw0. fdestr Hw0 Hw01 Hw02.
  fhave E : (u_fun0_app HG HR HOm HC g m tm w0 Hf Htm1 Hw01).
  fassert Ham : (a ∈' w0).
  { apply (sub0_use HG tm w0 a); [frew E (Sub0 tm`[↑] $0); exact (sub0_refl HG HR HOm HC tm)|].
    apply (sub0_use HG tn tm a Htm2). exact (sub0_use HG ta tn a Htn2 Hta2). }
  fassert Hbm : (b ∈' w0).
  { apply (sub0_use HG tm w0 b); [frew E (Sub0 tm`[↑] $0); exact (sub0_refl HG HR HOm HC tm)|].
    apply (sub0_use HG tn tm b Htm2). exact (sub0_use HG tb tn b Htn3 Htb2). }
  fassert Hcm : (c ∈' w0).
  { apply (sub0_use HG tm w0 c); [frew E (Sub0 tm`[↑] $0); exact (sub0_refl HG HR HOm HC tm)|].
    exact (sub0_use HG tc tm c Htm3 Htc2). }
  unfold Step in Hw02. pose proof (CE2 Hw02) as H3. finst H3 a. fmp H3 Ham. finst H3 b. fmp H3 Hbm. finst H3 c. fmp H3 Hcm.
  fhave T : (opsin_proj k ts a b c Hk H3). fex T y Hy. fdestr Hy Hy1 Hy2.
  fexists y. fsplit; [|exact Hy2]. exact (sub0_use HG ts C y (ran_sub HG HR HOm HC g C s ts Hu Hts) Hy1).
Qed.

(** ** Def0 *)
Lemma def_ex_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A :
  G ⊢C ∃ Def0 A`[↑] $0.
Proof.
  fobtain (u_succ0_ex HG HR HOm HC A) as S0 HS. fobtain (cl_ex_g HG HR HOm HC S0) as C HCl.
  pose proof (sep_use _ 1 S_sub (fun _ => A) C (in_S_sub _ HC) fb_S_sub) as T. unfold S_sub in T. simp_in T.
  fex T D HD. fexists D. unfold Def0. fexists S0. fexists C. fsplit; [fsplit; [fsplit; [exact HS|exact HCl]|]|].
  - fall z. fintro Hz. finst HD z. exact (iff_l _ _ _ HD Hz).
  - fall z. fintro Hz. fintro Hs. finst HD z. apply (iff_r _ _ _ HD). fsplit; assumption.
Qed.

Lemma def_unpack {G} (HG : incl ZF0base G) A D psi : G ⊢C Def0 A D ->
  (forall G' S0 C, incl G G' -> G' ⊢C Succ0 A S0 -> G' ⊢C Cl S0 C ->
     G' ⊢C ∀ ($0 ∈' D`[↑] → $0 ∈' C`[↑] ∧ Sub0 $0 A`[↑]) ->
     G' ⊢C ∀ ($0 ∈' C`[↑] → Sub0 $0 A`[↑] → $0 ∈' D`[↑]) -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  intros H K. pose proof (incl_refl G) as Hs. unfold Def0 in H. fex H S0 HS. fex HS C HCC.
  fdestr HCC Ha H4. fdestr Ha Hb H3. fdestr Hb H1 H2. exact (K _ S0 C Hs H1 H2 H3 H4).
Qed.

Lemma def_sub_g {G} (HG : incl ZF0base G) A D z : G ⊢C Def0 A D -> G ⊢C z ∈' D -> G ⊢C Sub0 z A.
Proof.
  intros H Hz. apply (def_unpack HG A D _ H). intros G1 S0 C H1 HS HCl H3 H4. wk H1.
  finst H3 z. exact (CE2 (IE H3 Hz)).
Qed.

Lemma def_unique_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A D D' :
  G ⊢C Def0 A D -> G ⊢C Def0 A D' -> G ⊢C sub' D D'.
Proof.
  intros H H'. apply (def_unpack HG A D _ H). intros G1 S0 C H1 HS HCl H3 H4. wk H1.
  apply (def_unpack HG A D' _ H'). intros G2 S0' C' H2 HS' HCl' H3' H4'. wk H2.
  fhave E : (u_succ0_unique HG HR HOm HC A S0 S0' HS HS'). frew_in E (Cl $0 C'`[↑]) HCl'.
  fhave Hcc : (cl_unique_g HG HR HOm HC S0 C C' HCl HCl').
  unfold sub'. fall z. fintro Hz. finst H3 z. fmp H3 Hz. fdestr H3 Hz1 Hz2.
  finst H4' z. fmp H4' (sub0_use HG C C' z Hcc Hz1). fmp H4' Hz2. exact H4'.
Qed.

Lemma def_self_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A D :
  G ⊢C Def0 A D -> G ⊢C A ∈' D.
Proof.
  intros H. apply (def_unpack HG A D _ H). intros G1 S0 C H1 HS HCl H3 H4. wk H1.
  finst H4 A. fmp H4 (cl_base_g HG HR HOm HC S0 C A HCl (succ0_self HG A S0 HS)).
  exact (IE H4 (sub0_refl HG HR HOm HC A)).
Qed.

Lemma def_trans_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A D :
  G ⊢C Trans0 A -> G ⊢C Def0 A D -> G ⊢C Sub0 A D.
Proof.
  intros HT H. apply (def_unpack HG A D _ H). intros G1 S0 C H1 HS HCl H3 H4. wk H1.
  unfold Sub0. fall x. fintro Hx. finst H4 x.
  fmp H4 (cl_base_g HG HR HOm HC S0 C x HCl (sub0_use HG A S0 x (succ0_sub HG A S0 HS) Hx)).
  apply (IE H4). unfold Trans0 in HT. finst HT x. fmp HT Hx. unfold Sub0. exact HT.
Qed.

(** the fact tactics also weaken hypotheses [forall k, k < n -> G ⊢C _] *)
Local Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : forall k : nat, @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k => weak_cons G a _ (H k)) as H'; clear H; rename H' into H
  | H : forall k : nat, k < ?n -> @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k Hk => weak_cons G a _ (H k Hk)) as H'; clear H; rename H' into H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  end.
Local Ltac wk' Hinc := match type of Hinc with incl ?A ?B =>
  repeat match goal with
  | H : A ⊢C _ |- _ => apply (fun h => Weak h Hinc) in H
  | H : forall k : nat, k < ?n -> @prv _ _ _ class A (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k Hk => Weak (H k Hk) Hinc) as H'; clear H; rename H' into H
  | H : incl ?X A |- _ => apply (fun h => incl_tran h Hinc) in H
  | H : In ?x A |- _ => apply Hinc in H
  end end.

(** ** Environments and numerals *)
(** [EnvF n sg e]: e = {(0, sg (n-1)), ..., (n-1, sg 0)} (the variable $k sits at position n-1-k) *)
Fixpoint EnvF (n : nat) (sg : nat -> term) (e : term) : form :=
  match n with
  | 0 => Emp0 e
  | S n' => ∃ (EnvF n' (fun k => (sg (S k))`[↑]) $0 ∧ Ext0 $0 (sg 0)`[↑] e`[↑])
  end.
(** [NumF k x]: x is the k-th von Neumann numeral *)
Fixpoint NumF (k : nat) (x : term) : form :=
  match k with 0 => Emp0 x | S k' => ∃ (NumF k' $0 ∧ Succ0 $0 x`[↑]) end.
#[global] Arguments EnvF : simpl never.
#[global] Arguments NumF : simpl never.
Lemma EnvF_0 sg e : EnvF 0 sg e = Emp0 e. Proof. reflexivity. Qed.
Lemma EnvF_S n sg e : EnvF (S n) sg e = ∃ (EnvF n (fun k => (sg (S k))`[↑]) $0 ∧ Ext0 $0 (sg 0)`[↑] e`[↑]).
Proof. reflexivity. Qed.
Lemma NumF_0 x : NumF 0 x = Emp0 x. Proof. reflexivity. Qed.
Lemma NumF_S k x : NumF (S k) x = ∃ (NumF k $0 ∧ Succ0 $0 x`[↑]). Proof. reflexivity. Qed.

Lemma EnvF_ext n : forall sg sg' e, (forall k, sg k = sg' k) -> EnvF n sg e = EnvF n sg' e.
Proof.
  induction n as [|n IH]; intros sg sg' e H; [reflexivity|]. rewrite !EnvF_S, (H 0).
  rewrite (IH (fun k => (sg (S k))`[↑]) (fun k => (sg' (S k))`[↑]) $0); [reflexivity|].
  intros k. cbn. now rewrite (H (S k)).
Qed.
Lemma EnvF_subst n : forall sg e tau, (EnvF n sg e)[tau] = EnvF n (fun k => (sg k)`[tau]) e`[tau].
Proof.
  induction n as [|n IH]; intros sg e tau; [apply Emp0_subst|]. rewrite !EnvF_S.
  change ((∃ (EnvF n (fun k => (sg (S k))`[↑]) $0 ∧ Ext0 $0 (sg 0)`[↑] e`[↑]))[tau])
    with (∃ ((EnvF n (fun k => (sg (S k))`[↑]) $0)[up tau] ∧ (Ext0 $0 (sg 0)`[↑] e`[↑])[up tau])).
  rewrite IH, Ext0_subst. rewrite !up_term.
  rewrite (EnvF_ext n (fun k => (sg (S k))`[↑]`[up tau]) (fun k => (sg (S k))`[tau]`[↑])) by (intros k; apply up_term).
  reflexivity.
Qed.
Lemma NumF_subst k : forall x tau, (NumF k x)[tau] = NumF k x`[tau].
Proof.
  induction k as [|k IH]; intros x tau; [apply Emp0_subst|]. rewrite !NumF_S.
  change ((∃ (NumF k $0 ∧ Succ0 $0 x`[↑]))[tau]) with (∃ ((NumF k $0)[up tau] ∧ (Succ0 $0 x`[↑])[up tau])).
  rewrite IH, Succ0_subst, up_term. reflexivity.
Qed.
Local Ltac fsz_xg ::= match goal with
  | |- context [ (EnvF ?n ?s ?e)[?t] ] => rewrite (EnvF_subst n s e t)
  | |- context [ (NumF ?n ?e)[?t] ] => rewrite (NumF_subst n e t)
  end.
Local Ltac fsz_xh H ::= match type of H with
  | context [ (EnvF ?n ?s ?e)[?t] ] => rewrite (EnvF_subst n s e t) in H
  | context [ (NumF ?n ?e)[?t] ] => rewrite (NumF_subst n e t) in H
  end.

Lemma env_E G n sg z psi : G ⊢C EnvF (S n) sg z ->
  (forall e, ((EnvF n (fun k => sg (S k)) e ∧ Ext0 e (sg 0) z) :: G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros H K. rewrite EnvF_S in H. apply (ExE_named H). intros e.
  assert (E : (EnvF n (fun k => (sg (S k))`[↑]) $0 ∧ Ext0 $0 (sg 0)`[↑] z`[↑])[e..] =
              (EnvF n (fun k => sg (S k)) e ∧ Ext0 e (sg 0) z)).
  { change ((EnvF n (fun k => (sg (S k))`[↑]) $0 ∧ Ext0 $0 (sg 0)`[↑] z`[↑])[e..]) with
      ((EnvF n (fun k => (sg (S k))`[↑]) $0)[e..] ∧ (Ext0 $0 (sg 0)`[↑] z`[↑])[e..]).
    rewrite EnvF_subst, Ext0_subst, !subst_term_shift.
    rewrite (EnvF_ext n _ (fun k => sg (S k))) by (intros k; apply subst_term_shift). reflexivity. }
  rewrite E. apply K.
Qed.
Lemma env_I G n sg e z : G ⊢C EnvF n (fun k => sg (S k)) e -> G ⊢C Ext0 e (sg 0) z -> G ⊢C EnvF (S n) sg z.
Proof.
  intros H1 H2. rewrite EnvF_S. apply (ExI e).
  change ((EnvF n (fun k => (sg (S k))`[↑]) $0 ∧ Ext0 $0 (sg 0)`[↑] z`[↑])[e..]) with
      ((EnvF n (fun k => (sg (S k))`[↑]) $0)[e..] ∧ (Ext0 $0 (sg 0)`[↑] z`[↑])[e..]).
  rewrite EnvF_subst, Ext0_subst, !subst_term_shift.
  rewrite (EnvF_ext n _ (fun k => sg (S k))) by (intros k; apply subst_term_shift). apply CI; assumption.
Qed.
Local Ltac fenv H e He1 He2 := apply (env_E _ _ _ _ _ H); intros e; let He := fresh "He" in ctx_push He;
  fdestr He He1 He2; try clear H.

Lemma scons_in {G} A v (sg : nat -> term) n : G ⊢C v ∈' A -> (forall k, k < n -> G ⊢C sg k ∈' A) ->
  forall k, k < S n -> G ⊢C (v .: sg) k ∈' A.
Proof. intros Hv Hs [|k] Hk; [exact Hv | apply Hs; lia]. Qed.

Section Num.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).

Lemma app_adj f q g u v : G ⊢C Adj f q g -> G ⊢C App0 g u v ↔ App0 f u v ∨ OP0 u v q.
Proof.
  intros Hg. fsplit.
  - fintro H. unfold App0 in H. fex H p Hp. fdestr Hp Hp1 Hp2. fhave E : (adj_el HG f q g p Hg Hp1). fcases E E1 E2.
    + fleft. exact (u_app0_intro HG HR HOm HC f u v p Hp2 E1).
    + fright. frew_in E2 (OP0 u`[↑] v`[↑] $0) Hp2. exact Hp2.
  - fintro H. fcases H H1 H2.
    + unfold App0 in H1. fex H1 p Hp. fdestr Hp Hp1 Hp2.
      exact (u_app0_intro HG HR HOm HC g u v p Hp2 (adj_in_l HG f q g p Hg Hp1)).
    + exact (u_app0_intro HG HR HOm HC g u v q H2 (adj_in_r HG f q g Hg)).
Qed.
End Num.

Lemma num_unique k : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) x x',
  G ⊢C NumF k x -> G ⊢C NumF k x' -> G ⊢C x ≡' x'.
Proof.
  induction k as [|k IH]; intros G HG HR HOm HC x x' H H'.
  - rewrite NumF_0 in H, H'. exact (u_emp0_unique HG HR HOm HC x x' H H').
  - rewrite NumF_S in H, H'. fex H y Hy. fdestr Hy Hy1 Hy2. fex H' y' Hy'. fdestr Hy' Hy1' Hy2'.
    fhave E : (IH _ HG HR HOm HC y y' Hy1 Hy1'). frew_in E (Succ0 $0 x'`[↑]) Hy2'.
    exact (u_succ0_unique HG HR HOm HC y x x' Hy2 Hy2').
Qed.

Lemma num_lt l : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) k x y,
  k < l -> G ⊢C NumF k x -> G ⊢C NumF l y -> G ⊢C x ∈' y.
Proof.
  induction l as [|l IH]; intros G HG HR HOm HC k x y Hk Hx Hy; [lia|].
  rewrite NumF_S in Hy. fex Hy y' Hy'. fdestr Hy' Hy1 Hy2. destruct (Nat.eq_dec k l) as [->|Hne].
  - fhave E : (num_unique l HG HR HOm HC x y' Hx Hy1). fhave H : (succ0_self HG y' y Hy2). fmem.
  - fhave H : (IH _ HG HR HOm HC k x y' ltac:(lia) Hx Hy1). exact (sub0_use HG y' y x (succ0_sub HG y' y Hy2) H).
Qed.

Lemma num_neq {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) k l x y :
  k <> l -> G ⊢C NumF k x -> G ⊢C NumF l y -> G ⊢C x ≡' y -> G ⊢C ⊥.
Proof.
  intros Hkl Hx Hy E. destruct (Nat.lt_ge_cases k l) as [H|H].
  - fhave H' : (num_lt l HG HR HOm HC k x y H Hx Hy). apply (u_no_self HG HR HOm HC y). fmem.
  - fhave H' : (num_lt k HG HR HOm HC l y x ltac:(lia) Hy Hx). apply (u_no_self HG HR HOm HC y). fmem.
Qed.

(** ** Facts about the closure C = Cl(A ∪ {A}) *)
Section CA.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).

Lemma clA_in A S0 C : G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C -> G ⊢C A ∈' C.
Proof. intros HS HCl. exact (cl_base_g HG HR HOm HC S0 C A HCl (succ0_self HG A S0 HS)). Qed.
Lemma clA_el A S0 C x : G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C -> G ⊢C x ∈' A -> G ⊢C x ∈' C.
Proof. intros HS HCl Hx. exact (cl_base_g HG HR HOm HC S0 C x HCl (sub0_use HG A S0 x (succ0_sub HG A S0 HS) Hx)). Qed.
Lemma cl_emp A S0 C : G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C -> G ⊢C ∃ (Emp0 $0 ∧ $0 ∈' C`[↑]).
Proof.
  intros HS HCl. fhave HA : (clA_in A S0 C HS HCl).
  fobtain (cl_op_g HG HR HOm HC 2 S0 C A A A ltac:(lia) HCl HA HA HA) as y Hy. fdestr Hy Hy1 Hy2.
  fhave D : (sepof_iff HG A y _ Hy2). fexists y. fsplit; [|exact Hy1]. unfold Emp0. fall z. fintro Hz.
  finst D z. fhave D' : (iff_l _ _ _ D Hz). fdestr D' D1 D2. exact (IE D2 D1).
Qed.
End CA.

Lemma num_inC k : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A S0 C,
  G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C -> G ⊢C ∃ (NumF k $0 ∧ $0 ∈' C`[↑]).
Proof.
  induction k as [|k IH]; intros G HG HR HOm HC A S0 C HS HCl.
  - fobtain (cl_emp HG HR HOm HC A S0 C HS HCl) as y Hy. fexists y. rewrite NumF_0. exact Hy.
  - fobtain (IH _ HG HR HOm HC A S0 C HS HCl) as x Hx. fdestr Hx Hx1 Hx2.
    fobtain (cl_op_g HG HR HOm HC 0 S0 C x x x ltac:(lia) HCl Hx2 Hx2 Hx2) as p Hp. fdestr Hp Hp1 Hp2.
    fobtain (cl_op_g HG HR HOm HC 0 S0 C x p p ltac:(lia) HCl Hx2 Hp1 Hp1) as q Hq. fdestr Hq Hq1 Hq2.
    fobtain (cl_op_g HG HR HOm HC 1 S0 C q q q ltac:(lia) HCl Hq1 Hq1 Hq1) as u Hu. fdestr Hu Hu1 Hu2.
    fexists u. fsplit; [|exact Hu1]. rewrite NumF_S. fexists x. fsplit; [exact Hx1|].
    unfold Succ0. fsplit; [fsplit|].
    + exact (union0_in HG q u p x Hu2 (pair0_r HG x p q Hq2) (pair0_l HG x x p Hp2)).
    + unfold Sub0. fall z. fintro Hz. exact (union0_in HG q u x z Hu2 (pair0_l HG x p q Hq2) Hz).
    + fall z. fintro Hz. fhave H : (union0_el HG q u z Hu2 Hz). fex H w Hw. fdestr Hw Hw1 Hw2.
      fhave E : (pair0_el HG x p q w Hq2 Hw1). fcases E E1 E2.
      * fleft. fmem.
      * fright. fassert Hzp : (z ∈' p). { fmem. } fhave E' : (pair0_el HG x x p z Hp2 Hzp). fcases E' E3 E4; feq.
Qed.

(** ** Environments: domain, lookup, the sets A^n *)
Lemma env_dom n : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) sg e d,
  G ⊢C EnvF n sg e -> G ⊢C NumF n d -> G ⊢C Dom0 e d.
Proof.
  induction n as [|n IH]; intros G HG HR HOm HC sg e d He Hd.
  - rewrite EnvF_0 in He. rewrite NumF_0 in Hd. apply (dom0_intro HG HR HOm HC).
    + intros G' u HGG' Hu. wk HGG'. fabsurd. exact (emp0_el HG d u Hd Hu).
    + intros G' u v HGG' Huv. wk HGG'. unfold App0 in Huv. fex Huv p Hp. fdestr Hp Hp1 Hp2.
      fabsurd. exact (emp0_el HG e p He Hp1).
  - rewrite NumF_S in Hd. fex Hd d' Hd'. fdestr Hd' Hd1 Hd2. fenv He e' He1 He2.
    fhave Hdom : (IH _ HG HR HOm HC _ e' d' He1 Hd1).
    fobtain (u_op0_ex HG HR HOm HC d' (sg 0)) as p Hp.
    fhave Ha : (ext0_char HG HR HOm HC e' (sg 0) e d' p He2 Hdom Hp).
    apply (dom0_intro HG HR HOm HC).
    + intros G' u HGG' Hu. wk HGG'. fhave E : (succ0_el HG d' d u Hd2 Hu). fcases E E1 E2.
      * fobtain (u_dom0_app HG HR HOm HC e' d' u Hdom E1) as w Hw. fexists w.
        exact (iff_r _ _ _ (app_adj HG HR HOm HC e' p e u w Ha) (DI1 _ Hw)).
      * fexists (sg 0). apply (iff_r _ _ _ (app_adj HG HR HOm HC e' p e u (sg 0) Ha)). fright.
        frew E2 (OP0 $0 (sg 0)`[↑] p`[↑]). exact Hp.
    + intros G' u v HGG' Huv. wk HGG'. fhave H : (iff_l _ _ _ (app_adj HG HR HOm HC e' p e u v Ha) Huv).
      fcases H H1 H2.
      * exact (sub0_use HG d' d u (succ0_sub HG d' d Hd2) (u_dom0_in HG HR HOm HC e' d' u v Hdom H1)).
      * fhave E : (CE1 (u_op0_inj HG HR HOm HC u v d' (sg 0) p H2 Hp)). fhave H3 : (succ0_self HG d' d Hd2). fmem.
Qed.

Lemma num_ex k : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G),
  G ⊢C ∃ NumF k $0.
Proof.
  induction k as [|k IH]; intros G HG HR HOm HC.
  - fobtain (u_emp0_ex HG HR HOm HC) as x Hx. fexists x. rewrite NumF_0. exact Hx.
  - fobtain (IH _ HG HR HOm HC) as x Hx. fobtain (u_succ0_ex HG HR HOm HC x) as s Hs.
    fexists s. rewrite NumF_S. fexists x. fsplit; assumption.
Qed.

Lemma env_app n : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) sg e i x w,
  G ⊢C EnvF n sg e -> i < n -> G ⊢C NumF (n - 1 - i) x -> G ⊢C App0 e x w ↔ w ≡' sg i.
Proof.
  induction n as [|n IH]; intros G HG HR HOm HC sg e i x w He Hi Hx; [lia|].
  fenv He e' He1 He2. fobtain (num_ex n HG HR HOm HC) as d Hd.
  fhave Hdom : (env_dom n HG HR HOm HC _ e' d He1 Hd).
  fobtain (u_op0_ex HG HR HOm HC d (sg 0)) as p Hp.
  fhave Ha : (ext0_char HG HR HOm HC e' (sg 0) e d p He2 Hdom Hp).
  fhave Hiff : (app_adj HG HR HOm HC e' p e x w Ha).
  destruct i as [|i].
  - replace (S n - 1 - 0) with n in Hx by lia. fhave E : (num_unique n HG HR HOm HC x d Hx Hd). fsplit.
    + fintro H. fhave H' : (iff_l _ _ _ Hiff H). fcases H' H1 H2.
      * fhave Hxd : (u_dom0_in HG HR HOm HC e' d x w Hdom H1). fabsurd. apply (u_no_self HG HR HOm HC d). fmem.
      * exact (CE2 (u_op0_inj HG HR HOm HC x w d (sg 0) p H2 Hp)).
    + fintro H. apply (iff_r _ _ _ Hiff). fright. frew E (OP0 $0 w`[↑] p`[↑]). frew H (OP0 d`[↑] $0 p`[↑]). exact Hp.
  - replace (S n - 1 - S i) with (n - 1 - i) in Hx by lia.
    fhave IHi : (IH _ HG HR HOm HC (fun k => sg (S k)) e' i x w He1 ltac:(lia) Hx). fsplit.
    + fintro H. fhave H' : (iff_l _ _ _ Hiff H). fcases H' H1 H2.
      * exact (iff_l _ _ _ IHi H1).
      * fabsurd. fhave E : (CE1 (u_op0_inj HG HR HOm HC x w d (sg 0) p H2 Hp)).
        exact (num_neq HG HR HOm HC (n - 1 - i) n x d ltac:(lia) Hx Hd E).
    + fintro H. apply (iff_r _ _ _ Hiff). fleft. exact (iff_r _ _ _ IHi H).
Qed.

Section AIE.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).

Lemma ai_env n sg e i j xi xj : G ⊢C EnvF n sg e -> i < n -> j < n -> G ⊢C NumF (n - 1 - i) xi ->
  G ⊢C NumF (n - 1 - j) xj -> G ⊢C AI xi xj e ↔ sg i ∈' sg j.
Proof.
  intros He Hi Hj Hxi Hxj. fsplit.
  - fintro H. unfold AI in H. fex H p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2.
    fex Hs2 t Ht. fdestr Ht Ht1 Ht2. fdestr Ht2 Hop Hq. fex Hq p' Hp'. fdestr Hp' Hp'1 Hp'2.
    fex Hp'2 s' Hs'. fdestr Hs' Hs'1 Hs'2. fex Hs'2 t' Ht'. fdestr Ht' Ht'1 Ht'2. fdestr Ht'2 Hop' Htt.
    fhave A1 : (u_app0_intro HG HR HOm HC e xi t p Hop Hp1).
    fhave E1 : (iff_l _ _ _ (env_app n HG HR HOm HC sg e i xi t He Hi Hxi) A1).
    fhave A2 : (u_app0_intro HG HR HOm HC e xj t' p' Hop' Hp'1).
    fhave E2 : (iff_l _ _ _ (env_app n HG HR HOm HC sg e j xj t' He Hj Hxj) A2).
    exact (elem_cong HG t t' (sg i) (sg j) E1 E2 Htt).
  - fintro H. fhave A1 : (iff_r _ _ _ (env_app n HG HR HOm HC sg e i xi (sg i) He Hi Hxi) (eq_refl' HG (sg i))).
    fhave A2 : (iff_r _ _ _ (env_app n HG HR HOm HC sg e j xj (sg j) He Hj Hxj) (eq_refl' HG (sg j))).
    unfold App0 in A1, A2. fex A1 p Hp. fdestr Hp Hp1 Hp2. fex A2 p' Hp'. fdestr Hp' Hp'1 Hp'2.
    fhave C1 : (op0_c2 HG xi (sg i) p Hp2). fex C1 s Hs. fdestr Hs Hs1 Hs2.
    fhave C2 : (op0_c2 HG xj (sg j) p' Hp'2). fex C2 s' Hs'. fdestr Hs' Hs'1 Hs'2.
    unfold AI. fexists p. fsplit; [exact Hp1|]. fexists s. fsplit; [exact Hs1|]. fexists (sg i). fsplit; [exact Hs2|].
    fsplit; [exact Hp2|]. fexists p'. fsplit; [exact Hp'1|]. fexists s'. fsplit; [exact Hs'1|].
    fexists (sg j). fsplit; [exact Hs'2|]. fsplit; [exact Hp'2|exact H].
Qed.

Lemma ae_env n sg e i j xi xj : G ⊢C EnvF n sg e -> i < n -> j < n -> G ⊢C NumF (n - 1 - i) xi ->
  G ⊢C NumF (n - 1 - j) xj -> G ⊢C AE xi xj e ↔ sg i ≡' sg j.
Proof.
  intros He Hi Hj Hxi Hxj. fsplit.
  - fintro H. unfold AE in H. fex H p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2.
    fex Hs2 t Ht. fdestr Ht Ht1 Ht2. fdestr Ht2 Hop Hq. fex Hq p' Hp'. fdestr Hp' Hp'1 Hp'2.
    fex Hp'2 s' Hs'. fdestr Hs' Hs'1 Hs'2. fex Hs'2 t' Ht'. fdestr Ht' Ht'1 Ht'2. fdestr Ht'2 Hop' Htt.
    fhave A1 : (u_app0_intro HG HR HOm HC e xi t p Hop Hp1).
    fhave E1 : (iff_l _ _ _ (env_app n HG HR HOm HC sg e i xi t He Hi Hxi) A1).
    fhave A2 : (u_app0_intro HG HR HOm HC e xj t' p' Hop' Hp'1).
    fhave E2 : (iff_l _ _ _ (env_app n HG HR HOm HC sg e j xj t' He Hj Hxj) A2).
    feq.
  - fintro H. fhave A1 : (iff_r _ _ _ (env_app n HG HR HOm HC sg e i xi (sg i) He Hi Hxi) (eq_refl' HG (sg i))).
    fhave A2 : (iff_r _ _ _ (env_app n HG HR HOm HC sg e j xj (sg j) He Hj Hxj) (eq_refl' HG (sg j))).
    unfold App0 in A1, A2. fex A1 p Hp. fdestr Hp Hp1 Hp2. fex A2 p' Hp'. fdestr Hp' Hp'1 Hp'2.
    fhave C1 : (op0_c2 HG xi (sg i) p Hp2). fex C1 s Hs. fdestr Hs Hs1 Hs2.
    fhave C2 : (op0_c2 HG xj (sg j) p' Hp'2). fex C2 s' Hs'. fdestr Hs' Hs'1 Hs'2.
    unfold AE. fexists p. fsplit; [exact Hp1|]. fexists s. fsplit; [exact Hs1|]. fexists (sg i). fsplit; [exact Hs2|].
    fsplit; [exact Hp2|]. fexists p'. fsplit; [exact Hp'1|]. fexists s'. fsplit; [exact Hs'1|].
    fexists (sg j). fsplit; [exact Hs'2|]. fsplit; [exact Hp'2|exact H].
Qed.
End AIE.

(** every environment of length n over A lies in the set An = A^n *)
Definition EnvIn (G : list form) (A An : term) (n : nat) : Prop :=
  forall G' sg e, incl G G' -> (forall k, k < n -> G' ⊢C sg k ∈' A) -> G' ⊢C EnvF n sg e -> G' ⊢C e ∈' An.

Lemma an_ex n : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A S0 C psi,
  G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C ->
  (forall G' An, incl G G' -> G' ⊢C An ∈' C -> EnvIn G' A An n -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  induction n as [|n IH]; intros G HG HR HOm HC A S0 C psi HS HCl K; pose proof (incl_refl G) as Hs.
  - fobtain (cl_emp HG HR HOm HC A S0 C HS HCl) as e0 He0. fdestr He0 He01 He02.
    fobtain (cl_op_g HG HR HOm HC 0 S0 C e0 e0 e0 ltac:(lia) HCl He02 He02 He02) as An HAn. fdestr HAn HAn1 HAn2.
    apply (K _ An Hs HAn1). intros G' sg e HGG' Hsg He. wk' HGG'. rewrite EnvF_0 in He.
    fhave E : (u_emp0_unique HG HR HOm HC e e0 He He01). fhave H : (pair0_l HG e0 e0 An HAn2). fmem.
  - apply (IH G HG HR HOm HC A S0 C psi HS HCl). intros G1 An H1 HAn HEnv. pose proof (incl_refl G1) as Hs1. wk' H1.
    fhave HA : (clA_in HG HR HOm HC A S0 C HS HCl).
    fobtain (cl_op_g HG HR HOm HC 3 S0 C An A A ltac:(lia) HCl HAn HA HA) as An1 HAn1. fdestr HAn1 HA1 HA2.
    apply (K _ An1 Hs HA1). intros G' sg z HGG' Hsg Hz. wk' HGG'. fenv Hz e He1 He2.
    fhave Hein : (HEnv _ (fun k => sg (S k)) e Hs1 (fun k Hk => Hsg (S k) ltac:(lia)) He1).
    pose proof (CE2 HA2) as H3. finst H3 e. fmp H3 Hein. finst H3 (sg 0). fmp H3 (Hsg 0 ltac:(lia)).
    fex H3 y Hy. fdestr Hy Hy1 Hy2. fhave E : (ext0_unique HG HR HOm HC e (sg 0) y z Hy2 He2). fmem.
Qed.

(** the environment of finitely many elements of A lies in C *)
Lemma env_inC m : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G)
  A S0 C sg psi, G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C -> (forall k, k < m -> G ⊢C sg k ∈' A) ->
  (forall G' s, incl G G' -> G' ⊢C s ∈' C -> G' ⊢C EnvF m sg s -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  induction m as [|m IH]; intros G HG HR HOm HC A S0 C sg psi HS HCl Hsg K; pose proof (incl_refl G) as Hs.
  - fobtain (cl_emp HG HR HOm HC A S0 C HS HCl) as s Hs0. fdestr Hs0 Hs1 Hs2. apply (K _ s Hs Hs2).
    rewrite EnvF_0. exact Hs1.
  - apply (IH G HG HR HOm HC A S0 C (fun k => sg (S k)) psi HS HCl (fun k Hk => Hsg (S k) ltac:(lia))).
    intros G1 s' H1 Hs'C Hs'e. wk' H1.
    fhave Hv : (clA_el HG HR HOm HC A S0 C (sg 0) HS HCl (Hsg 0 ltac:(lia))).
    fobtain (cl_op_g HG HR HOm HC 0 S0 C s' s' s' ltac:(lia) HCl Hs'C Hs'C Hs'C) as p1 Hp1. fdestr Hp1 Hp11 Hp12.
    fobtain (cl_op_g HG HR HOm HC 0 S0 C (sg 0) (sg 0) (sg 0) ltac:(lia) HCl Hv Hv Hv) as p2 Hp2. fdestr Hp2 Hp21 Hp22.
    fobtain (cl_op_g HG HR HOm HC 3 S0 C p1 p2 p2 ltac:(lia) HCl Hp11 Hp21 Hp21) as Tt HT. fdestr HT HT1 HT2.
    fobtain (cl_op_g HG HR HOm HC 1 S0 C Tt Tt Tt ltac:(lia) HCl HT1 HT1 HT1) as z Hz. fdestr Hz Hz1 Hz2.
    fobtain (ext0_ex HG HR HOm HC s' (sg 0)) as z0 Hz0.
    fassert Hz0T : (z0 ∈' Tt).
    { pose proof (CE2 HT2) as H3. finst H3 s'. fmp H3 (pair0_l HG s' s' p1 Hp12). finst H3 (sg 0).
      fmp H3 (pair0_l HG (sg 0) (sg 0) p2 Hp22). fex H3 y Hy. fdestr Hy Hy1 Hy2.
      fhave E : (ext0_unique HG HR HOm HC s' (sg 0) y z0 Hy2 Hz0). fmem. }
    fassert E : (z0 ≡' z).
    { apply (ext_rule HG); unfold sub'; fall w; fintro Hw.
      - exact (union0_in HG Tt z z0 w Hz2 Hz0T Hw).
      - fhave H : (union0_el HG Tt z w Hz2 Hw). fex H y Hy. fdestr Hy Hy1 Hy2.
        pose proof (CE1 HT2) as H3. finst H3 y. fmp H3 Hy1. fex H3 e1 He1. fdestr He1 He11 He12.
        fex He12 v1 Hv1. fdestr Hv1 Hv11 Hv12.
        fhave E1 : (pair0_el HG s' s' p1 e1 Hp12 He11). fhave E2 : (pair0_el HG (sg 0) (sg 0) p2 v1 Hp22 Hv11).
        fassert E1' : (e1 ≡' s'). { fcases E1 A1 A2; assumption. }
        fassert E2' : (v1 ≡' sg 0). { fcases E2 A1 A2; assumption. }
        frew_in E1' (Ext0 $0 v1`[↑] y`[↑]) Hv12. frew_in E2' (Ext0 s'`[↑] $0 y`[↑]) Hv12.
        fhave E3 : (ext0_unique HG HR HOm HC s' (sg 0) y z0 Hv12 Hz0). fmem. }
    frew_in E (Ext0 s'`[↑] (sg 0)`[↑] $0) Hz0.
    apply (K _ z Hs Hz1). exact (env_I _ m sg s' z Hs'e Hz0).
Qed.

(** ** The definability lemma *)
(** [Rep G A R n phi]: R represents phi (free variables among $0..$(n-1)) on A: for every
    assignment sg of elements of A and its environment e, e ∈ R ↔ φ^A[sg] *)
Definition Rep (G : list form) (A R : term) (n : nat) (phi : form) : Prop :=
  forall G' sg e, incl G G' -> (forall k, k < n -> G' ⊢C sg k ∈' A) -> G' ⊢C EnvF n sg e ->
    G' ⊢C e ∈' R ↔ relS A (phi[sg]).

Lemma rep_ex (phi : form) : forall n {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HC : incl Ax_cl G) A S0 C psi, fb n phi -> G ⊢C Succ0 A S0 -> G ⊢C Cl S0 C ->
  (forall G' R, incl G G' -> G' ⊢C R ∈' C -> Rep G' A R n phi -> G' ⊢C psi) -> G ⊢C psi.
Proof.
  induction phi as [| P v | b phi1 IH1 phi2 IH2 | q psi0 IH] using form_ind_falsity;
    intros n G HG HR HOm HC A S0 C psi Hfb HS HCl K; pose proof (incl_refl G) as Hs.
  - (* ⊥ *)
    fobtain (cl_emp HG HR HOm HC A S0 C HS HCl) as R HR0. fdestr HR0 HR1 HR2. apply (K _ R Hs HR2).
    intros G' sg e HGG' Hsg He. wk' HGG'. cbn. fsplit.
    + fintro H. exact (emp0_el HG R e HR1 H).
    + fintro H. fabsurd. exact H.
  - (* atoms *)
    apply (an_ex n HG HR HOm HC A S0 C psi HS HCl). intros G1 An Hi1 HAn HEnv. pose proof (incl_refl G1) as T1. wk' Hi1.
    destruct P; cbn in v, Hfb; rewrite (vec2 v) in Hfb, K; cbn in Hfb;
      destruct (Vector.hd v) as [i|[]]; destruct (Vector.hd (Vector.tl v)) as [j|[]]; cbn in Hfb; destruct Hfb as [Hi Hj].
    + fobtain (num_inC (n - 1 - i) HG HR HOm HC A S0 C HS HCl) as xi Hxi. fdestr Hxi Hxi1 Hxi2.
      fobtain (num_inC (n - 1 - j) HG HR HOm HC A S0 C HS HCl) as xj Hxj. fdestr Hxj Hxj1 Hxj2.
      fobtain (cl_op_g HG HR HOm HC 6 S0 C An xi xj ltac:(lia) HCl HAn Hxi2 Hxj2) as R HR0. fdestr HR0 HR1 HR2.
      apply (K _ R Hs HR1). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave D : (sepof_iff HG An R _ HR2). finst D e. fhave Hin : (HEnv _ sg e T1 Hsg He).
      fhave I : (ai_env HG HR HOm HC n sg e i j xi xj He Hi Hj Hxi1 Hxj1). fsplit.
      * fintro H. exact (iff_l _ _ _ I (CE2 (iff_l _ _ _ D H))).
      * fintro H. apply (iff_r _ _ _ D). fsplit; [exact Hin | exact (iff_r _ _ _ I H)].
    + fobtain (num_inC (n - 1 - i) HG HR HOm HC A S0 C HS HCl) as xi Hxi. fdestr Hxi Hxi1 Hxi2.
      fobtain (num_inC (n - 1 - j) HG HR HOm HC A S0 C HS HCl) as xj Hxj. fdestr Hxj Hxj1 Hxj2.
      fobtain (cl_op_g HG HR HOm HC 7 S0 C An xi xj ltac:(lia) HCl HAn Hxi2 Hxj2) as R HR0. fdestr HR0 HR1 HR2.
      apply (K _ R Hs HR1). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave D : (sepof_iff HG An R _ HR2). finst D e. fhave Hin : (HEnv _ sg e T1 Hsg He).
      fhave I : (ae_env HG HR HOm HC n sg e i j xi xj He Hi Hj Hxi1 Hxj1). fsplit.
      * fintro H. exact (iff_l _ _ _ I (CE2 (iff_l _ _ _ D H))).
      * fintro H. apply (iff_r _ _ _ D). fsplit; [exact Hin | exact (iff_r _ _ _ I H)].
  - (* binary connectives *)
    cbn in Hfb. destruct Hfb as [Hfb1 Hfb2].
    apply (IH1 n G HG HR HOm HC A S0 C psi Hfb1 HS HCl). intros G1 R1 Hi1 HR1 Rep1. pose proof (incl_refl G1) as T1. wk' Hi1.
    apply (IH2 n _ HG HR HOm HC A S0 C psi Hfb2 HS HCl). intros G2 R2 Hi2 HR2 Rep2. pose proof (incl_refl G2) as T2. wk' Hi2.
    destruct b.
    + (* ∧ : R1 − (R1 − R2) *)
      fobtain (cl_op_g HG HR HOm HC 2 S0 C R1 R2 R2 ltac:(lia) HCl HR1 HR2 HR2) as R' HR'. fdestr HR' HR'1 HR'2.
      fobtain (cl_op_g HG HR HOm HC 2 S0 C R1 R' R' ltac:(lia) HCl HR1 HR'1 HR'1) as R HR0. fdestr HR0 HR01 HR02.
      apply (K _ R Hs HR01). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave I1 : (Rep1 _ sg e T1 Hsg He). fhave I2 : (Rep2 _ sg e T2 Hsg He).
      fhave D : (sepof_iff HG R1 R _ HR02). finst D e. fhave D' : (sepof_iff HG R1 R' _ HR'2). finst D' e. fsplit.
      * fintro H. fhave H' : (iff_l _ _ _ D H). fdestr H' Ha Hb. fsplit; [exact (iff_l _ _ _ I1 Ha)|].
        apply (iff_l _ _ _ I2). fcontra Hc. apply (IE Hb). apply (iff_r _ _ _ D'). fsplit; [exact Ha|exact Hc].
      * fintro H. fdestr H Ha Hb. apply (iff_r _ _ _ D). fsplit; [exact (iff_r _ _ _ I1 Ha)|].
        fintro Hc. fhave Hc' : (iff_l _ _ _ D' Hc). fdestr Hc' Hc1 Hc2. exact (IE Hc2 (iff_r _ _ _ I2 Hb)).
    + (* ∨ : ⋃{R1, R2} *)
      fobtain (cl_op_g HG HR HOm HC 0 S0 C R1 R2 R2 ltac:(lia) HCl HR1 HR2 HR2) as Pp HP. fdestr HP HP1 HP2.
      fobtain (cl_op_g HG HR HOm HC 1 S0 C Pp Pp Pp ltac:(lia) HCl HP1 HP1 HP1) as R HR0. fdestr HR0 HR01 HR02.
      apply (K _ R Hs HR01). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave I1 : (Rep1 _ sg e T1 Hsg He). fhave I2 : (Rep2 _ sg e T2 Hsg He). fsplit.
      * fintro H. fhave H' : (union0_el HG Pp R e HR02 H). fex H' y Hy. fdestr Hy Hy1 Hy2.
        fhave E : (pair0_el HG R1 R2 Pp y HP2 Hy1). fcases E E1 E2.
        -- fleft. apply (iff_l _ _ _ I1). fmem.
        -- fright. apply (iff_l _ _ _ I2). fmem.
      * fintro H. fcases H H1 H2.
        -- exact (union0_in HG Pp R R1 e HR02 (pair0_l HG R1 R2 Pp HP2) (iff_r _ _ _ I1 H1)).
        -- exact (union0_in HG Pp R R2 e HR02 (pair0_r HG R1 R2 Pp HP2) (iff_r _ _ _ I2 H2)).
    + (* → : ⋃{An − R1, R2} *)
      apply (an_ex n HG HR HOm HC A S0 C psi HS HCl). intros G3 An Hi3 HAn HEnv. pose proof (incl_refl G3) as T3. wk' Hi3.
      fobtain (cl_op_g HG HR HOm HC 2 S0 C An R1 R1 ltac:(lia) HCl HAn HR1 HR1) as N HN. fdestr HN HN1 HN2.
      fobtain (cl_op_g HG HR HOm HC 0 S0 C N R2 R2 ltac:(lia) HCl HN1 HR2 HR2) as Pp HP. fdestr HP HP1 HP2.
      fobtain (cl_op_g HG HR HOm HC 1 S0 C Pp Pp Pp ltac:(lia) HCl HP1 HP1 HP1) as R HR0. fdestr HR0 HR01 HR02.
      apply (K _ R Hs HR01). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave I1 : (Rep1 _ sg e T1 Hsg He). fhave I2 : (Rep2 _ sg e T2 Hsg He). fhave Hin : (HEnv _ sg e T3 Hsg He).
      fhave D : (sepof_iff HG An N _ HN2). finst D e. fsplit.
      * fintro H. fintro H1. fhave H' : (union0_el HG Pp R e HR02 H). fex H' y Hy. fdestr Hy Hy1 Hy2.
        fhave E : (pair0_el HG N R2 Pp y HP2 Hy1). fcases E E1 E2.
        -- fassert HeN : (e ∈' N). { fmem. } fhave HeN' : (iff_l _ _ _ D HeN). fabsurd.
           exact (IE (CE2 HeN') (iff_r _ _ _ I1 H1)).
        -- apply (iff_l _ _ _ I2). fmem.
      * fintro H. apply (XM_rule _ (relS A (phi1[sg]))).
        -- fintro H1. fmp H H1. exact (union0_in HG Pp R R2 e HR02 (pair0_r HG N R2 Pp HP2) (iff_r _ _ _ I2 H)).
        -- fintro H1. apply (union0_in HG Pp R N e HR02 (pair0_l HG N R2 Pp HP2)). apply (iff_r _ _ _ D).
           fsplit; [exact Hin|]. fintro H2. exact (IE H1 (iff_l _ _ _ I1 H2)).
  - (* quantifiers *)
    cbn in Hfb.
    apply (IH (S n) G HG HR HOm HC A S0 C psi Hfb HS HCl). intros G1 R' Hi1 HR' Rep'. pose proof (incl_refl G1) as T1. wk' Hi1.
    apply (an_ex n HG HR HOm HC A S0 C psi HS HCl). intros G2 An Hi2 HAn HEnv. pose proof (incl_refl G2) as T2. wk' Hi2.
    fhave HA : (clA_in HG HR HOm HC A S0 C HS HCl). destruct q.
    + (* ∀ : An − proj(A^{n+1} − R') *)
      apply (an_ex (S n) HG HR HOm HC A S0 C psi HS HCl). intros G3 An1 Hi3 HAn1 HEnv1. pose proof (incl_refl G3) as T3. wk' Hi3.
      fobtain (cl_op_g HG HR HOm HC 2 S0 C An1 R' R' ltac:(lia) HCl HAn1 HR' HR') as N HN. fdestr HN HN1 HN2.
      fobtain (cl_op_g HG HR HOm HC 4 S0 C An N A ltac:(lia) HCl HAn HN1 HA) as Pp HP. fdestr HP HP1 HP2.
      fobtain (cl_op_g HG HR HOm HC 2 S0 C An Pp Pp ltac:(lia) HCl HAn HP1 HP1) as R HR0. fdestr HR0 HR01 HR02.
      apply (K _ R Hs HR01). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave Hin : (HEnv _ sg e T2 Hsg He).
      fhave D : (sepof_iff HG An R _ HR02). finst D e. fhave DP : (sepof_iff HG An Pp _ HP2). finst DP e.
      fhave DN : (sepof_iff HG An1 N _ HN2). fsplit.
      * fintro H. fhave H' : (CE2 (iff_l _ _ _ D H)). fall v. fintro Hv.
        fobtain (ext0_ex HG HR HOm HC e v) as z Hz. fhave Henv : (env_I _ n (v .: sg) e z He Hz).
        fhave Iz : (Rep' _ (v .: sg) z T1 (scons_in A v sg n Hv Hsg) Henv).
        fcontra Hn. apply (IE H'). apply (iff_r _ _ _ DP). fsplit; [exact Hin|]. unfold PJ.
        fexists v. fsplit; [exact Hv|]. fexists z. fsplit; [|exact Hz]. finst DN z. apply (iff_r _ _ _ DN).
        fsplit; [exact (HEnv1 _ (v .: sg) z T3 (scons_in A v sg n Hv Hsg) Henv)|].
        fintro Hz'. exact (IE Hn (iff_l _ _ _ Iz Hz')).
      * fintro H. apply (iff_r _ _ _ D). fsplit; [exact Hin|]. fintro Hp. fhave Hp' : (CE2 (iff_l _ _ _ DP Hp)).
        unfold PJ in Hp'. fex Hp' v Hv. fdestr Hv Hv1 Hv2. fex Hv2 z Hz. fdestr Hz Hz1 Hz2.
        fhave Henv : (env_I _ n (v .: sg) e z He Hz2).
        fhave Iz : (Rep' _ (v .: sg) z T1 (scons_in A v sg n Hv1 Hsg) Henv).
        finst DN z. fhave Hz3 : (CE2 (iff_l _ _ _ DN Hz1)). finst H v. fmp H Hv1. exact (IE Hz3 (iff_r _ _ _ Iz H)).
    + (* ∃ : proj(R') *)
      fobtain (cl_op_g HG HR HOm HC 4 S0 C An R' A ltac:(lia) HCl HAn HR' HA) as R HR0. fdestr HR0 HR01 HR02.
      apply (K _ R Hs HR01). intros G' sg e HGG' Hsg He. wk' HGG'. cbn.
      fhave Hin : (HEnv _ sg e T2 Hsg He). fhave D : (sepof_iff HG An R _ HR02). finst D e. fsplit.
      * fintro H. fhave H' : (CE2 (iff_l _ _ _ D H)). unfold PJ in H'. fex H' v Hv. fdestr Hv Hv1 Hv2.
        fex Hv2 z Hz. fdestr Hz Hz1 Hz2.
        fhave Henv : (env_I _ n (v .: sg) e z He Hz2).
        fhave Iz : (Rep' _ (v .: sg) z T1 (scons_in A v sg n Hv1 Hsg) Henv).
        fexists v. fsplit; [exact Hv1|exact (iff_l _ _ _ Iz Hz1)].
      * fintro H. fex H v Hv. fdestr Hv Hv1 Hv2. fobtain (ext0_ex HG HR HOm HC e v) as z Hz.
        fhave Henv : (env_I _ n (v .: sg) e z He Hz).
        fhave Iz : (Rep' _ (v .: sg) z T1 (scons_in A v sg n Hv1 Hsg) Henv).
        apply (iff_r _ _ _ D). fsplit; [exact Hin|]. unfold PJ. fexists v. fsplit; [exact Hv1|].
        fexists z. fsplit; [exact (iff_r _ _ _ Iz Hv2)|exact Hz].
Qed.

Lemma definable_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) m phi sg A D :
  fb (S m) phi -> G ⊢C Def0 A D -> (forall k, k < m -> G ⊢C sg k ∈' A) ->
  G ⊢C ∃ ($0 ∈' D`[↑] ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' A`[↑]`[↑] ∧ relS A`[↑]`[↑] (phi[up (sg >> subst_term ↑)]))).
Proof.
  intros Hfb HD Hsg.
  apply (def_unpack HG A D _ HD). intros G1 S0 C H1 HS HCl HD1 HD2. wk' H1.
  apply (rep_ex phi (S m) HG HR HOm HC A S0 C _ Hfb HS HCl). intros G2 R H2 HRC Hrep. pose proof (incl_refl G2) as T2. wk' H2.
  apply (env_inC m HG HR HOm HC A S0 C sg _ HS HCl Hsg). intros G3 s H3 HsC Hse. wk' H3.
  fhave HA : (clA_in HG HR HOm HC A S0 C HS HCl).
  fobtain (cl_op_g HG HR HOm HC 5 S0 C R s A ltac:(lia) HCl HRC HsC HA) as Y HY. fdestr HY HY1 HY2.
  fhave DY : (sepof_iff HG A Y _ HY2).
  fexists Y. fsplit.
  - finst HD2 Y. fmp HD2 HY1. apply (IE HD2). unfold Sub0. fall x. fintro Hx. finst DY x. exact (CE1 (iff_l _ _ _ DY Hx)).
  - fall x.
    match goal with |- context [ relS ?A' (phi[?s1][?s2]) ] =>
      replace (phi[s1][s2]) with (phi[x .: sg]) by (rewrite subst_comp; apply subst_ext; intros [|k]; term_eq) end.
    finst DY x. fsplit.
    + fintro Hx. fhave Hx' : (iff_l _ _ _ DY Hx). fdestr Hx' Hx1 Hx2. fsplit; [exact Hx1|].
      unfold SC in Hx2. fex Hx2 z Hz. fdestr Hz Hz1 Hz2.
      fhave Henv : (env_I _ m (x .: sg) s z Hse Hz2).
      fhave Iz : (Hrep _ (x .: sg) z T2 (scons_in A x sg m Hx1 Hsg) Henv). exact (iff_l _ _ _ Iz Hz1).
    + fintro Hx. fdestr Hx Hx1 Hx2. fobtain (ext0_ex HG HR HOm HC s x) as z Hz.
      fhave Henv : (env_I _ m (x .: sg) s z Hse Hz).
      fhave Iz : (Hrep _ (x .: sg) z T2 (scons_in A x sg m Hx1 Hsg) Henv).
      apply (iff_r _ _ _ DY). fsplit; [exact Hx1|]. unfold SC. fexists z. fsplit; [exact (iff_r _ _ _ Iz Hx2)|exact Hz].
Qed.

Section Cl.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G).

Lemma step_ex X : G ⊢C ∃ Step X`[↑] $0.
Proof. exact (step_ex_g HG HR HOm HC X). Qed.
Lemma step_unique X Y Y' : G ⊢C Step X Y -> G ⊢C Step X Y' -> G ⊢C Y ≡' Y'.
Proof. intros H1 H2. exact (step_unique_g HG HR HOm HC X Y Y' H1 H2). Qed.

Lemma Scl_loc B : G ⊢C SLoc Scl B.
Proof. exact (Scl_loc_g HG HR HOm HC B). Qed.
Lemma Scl_tot B : G ⊢C STot Scl B.
Proof. exact (Scl_tot_g HG HR HOm HC B). Qed.
Lemma Scl_fun B : G ⊢C SFun Scl B.
Proof. exact (Scl_fun_g HG HR HOm HC B). Qed.

Lemma cl_ex B : G ⊢C ∃ Cl B`[↑] $0.
Proof. exact (cl_ex_g HG HR HOm HC B). Qed.
Lemma cl_unique B C C' : G ⊢C Cl B C -> G ⊢C Cl B C' -> G ⊢C C ≡' C'.
Proof. intros H1 H2. exact (ext_rule HG C C' (cl_unique_g HG HR HOm HC B C C' H1 H2) (cl_unique_g HG HR HOm HC B C' C H2 H1)). Qed.
Lemma cl_base B C x : G ⊢C Cl B C -> G ⊢C x ∈' B -> G ⊢C x ∈' C.
Proof. exact (cl_base_g HG HR HOm HC B C x). Qed.
Lemma cl_op k B C a b c : k < 8 -> G ⊢C Cl B C -> G ⊢C a ∈' C -> G ⊢C b ∈' C -> G ⊢C c ∈' C ->
  G ⊢C ∃ ($0 ∈' C`[↑] ∧ Op k a`[↑] b`[↑] c`[↑] $0).
Proof. exact (cl_op_g HG HR HOm HC k B C a b c). Qed.

Lemma def_ex A : G ⊢C ∃ Def0 A`[↑] $0.
Proof. exact (def_ex_g HG HR HOm HC A). Qed.
Lemma def_unique A D D' : G ⊢C Def0 A D -> G ⊢C Def0 A D' -> G ⊢C D ≡' D'.
Proof. intros H1 H2. exact (ext_rule HG D D' (def_unique_g HG HR HOm HC A D D' H1 H2) (def_unique_g HG HR HOm HC A D' D H2 H1)). Qed.
Lemma def_sub A D z : G ⊢C Def0 A D -> G ⊢C z ∈' D -> G ⊢C Sub0 z A.
Proof. exact (def_sub_g HG A D z). Qed.

(** the definability lemma: for φ with free variables among $0 (the element) and $1..$m
    (parameters [sg 0 .. sg (m-1)], all in A), {x ∈ A | φ^A(x, sg)} ∈ Def(A) *)
Theorem definable m phi sg A D : fb (S m) phi -> G ⊢C Def0 A D ->
  (forall k, k < m -> G ⊢C sg k ∈' A) ->
  G ⊢C ∃ ($0 ∈' D`[↑] ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' A`[↑]`[↑] ∧ relS A`[↑]`[↑] (phi[up (sg >> subst_term ↑)]))).
Proof. exact (definable_g HG HR HOm HC m phi sg A D). Qed.

Lemma def_self A D : G ⊢C Def0 A D -> G ⊢C A ∈' D.
Proof. exact (def_self_g HG HR HOm HC A D). Qed.
Lemma def_trans A D : G ⊢C Trans0 A -> G ⊢C Def0 A D -> G ⊢C Sub0 A D.
Proof. exact (def_trans_g HG HR HOm HC A D). Qed.

End Cl.


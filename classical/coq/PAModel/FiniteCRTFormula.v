(** Reification of the internal CRT induction invariant in the ordinary
    first-order PA language.  The relation R is supplied by one formula. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition congruent_formula (q x y : term) : form :=
  ∃∃ x`[↑]`[↑] ⊕ (q`[↑]`[↑] ⊗ $1) == y`[↑]`[↑] ⊕ (q`[↑]`[↑] ⊗ $0).

Definition unit_formula (a q : term) : form :=
  ∃ congruent_formula q`[↑] (a`[↑] ⊗ $0) (σ zero).

Definition divides_formula (q m : term) : form := ∃ m`[↑] == q`[↑] ⊗ $0.

Definition modulus_term (c i : term) : term := σ ((σ i) ⊗ c).

Lemma holds_exists (M : Model) rho phi :
  holds M rho (∃ phi) <-> exists x, holds M (x .: rho) phi.
Proof. reflexivity. Qed.
Lemma holds_forall (M : Model) rho phi :
  holds M rho (∀ phi) <-> forall x, holds M (x .: rho) phi.
Proof. reflexivity. Qed.
Lemma holds_and (M : Model) rho phi psi :
  holds M rho (phi ∧ psi) <-> holds M rho phi /\ holds M rho psi.
Proof. reflexivity. Qed.
Lemma holds_imp (M : Model) rho phi psi :
  holds M rho (phi → psi) <-> (holds M rho phi -> holds M rho psi).
Proof. reflexivity. Qed.

Lemma holds_sless (M : Model) rho x y :
  holds M rho (Peano.sless x y) <-> coding_lt M (evalM M rho x) (evalM M rho y).
Proof.
  unfold holds,Peano.sless,coding_lt,evalM. cbn.
  split; intros [d Hd]; exists d.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d) in Hd. exact Hd.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d). exact Hd.
Qed.

Lemma holds_congruent (M : Model) rho q x y :
  holds M rho (congruent_formula q x y) <->
  congruent M (evalM M rho q) (evalM M rho x) (evalM M rho y).
Proof.
  unfold holds,congruent_formula,congruent,evalM. cbn.
  split; intros [a [b H]]; exists a,b.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) (a .: rho) b),
      !(@eval_up _ _ (carrier M) (interpretation M) rho a) in H. exact H.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) (a .: rho) b),
      !(@eval_up _ _ (carrier M) (interpretation M) rho a). exact H.
Qed.

Lemma holds_unit (M : Model) rho a q :
  holds M rho (unit_formula a q) <->
  unit_modulo M (evalM M rho a) (evalM M rho q).
Proof.
  unfold unit_formula,unit_modulo. rewrite holds_exists.
  split; intros [u H]; exists u.
  - apply holds_congruent in H. unfold evalM in H. cbn in H.
    rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho u) in H. exact H.
  - apply holds_congruent. unfold evalM. cbn.
    rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho u). exact H.
Qed.

Lemma holds_divides (M : Model) rho q m :
  holds M rho (divides_formula q m) <->
    exists d, evalM M rho m = mulM M (evalM M rho q) d.
Proof.
  unfold holds,divides_formula,evalM. cbn.
  split; intros [d H]; exists d.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d) in H. exact H.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d). exact H.
Qed.

(** At the occurrence of theta, the context is r,j,m,b,k,c,n,rho. *)
Definition read_relation (theta : form) : form :=
  theta[($0 .: $1 .: fun x => var (7+x))].

Definition crt_stage_formula (theta : form) : form :=
  ∃∃
   ((∀ (Peano.sless $0 $3 →
      ∃ (read_relation theta ∧ congruent_formula (modulus_term $5 $1) $3 $0))) ∧
    ((∀ (Peano.sless $0 $3 → divides_formula (modulus_term $4 $0) $1)) ∧
     (∀ (Peano.sless $3 (σ $0) → Peano.sless $0 $5 →
       unit_formula $1 (modulus_term $4 $0))))).

Lemma holds_read_relation (M : Model) rho theta r j m b k c n :
  holds M (r .: j .: m .: b .: k .: c .: n .: rho) (read_relation theta) <->
  holds M (r .: j .: rho) theta.
Proof.
  unfold holds,read_relation. rewrite sat_comp. apply sat_ext.
  intros [|[|x]]; reflexivity.
Qed.

Local Lemma iff_ex_congr {A : Type} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> ((exists x, P x) <-> (exists x, Q x)).
Proof. firstorder. Qed.
Local Lemma iff_all_congr {A : Type} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).
Proof. firstorder. Qed.
Local Lemma iff_and_congr P Q R S :
  (P <-> R) -> (Q <-> S) -> ((P /\ Q) <-> (R /\ S)).
Proof. tauto. Qed.
Local Lemma iff_imp_congr P Q R S :
  (P <-> R) -> (Q <-> S) -> ((P -> Q) <-> (R -> S)).
Proof. tauto. Qed.

Lemma holds_crt_stage (M : Model) rho theta k c n :
  holds M (k .: c .: n .: rho) (crt_stage_formula theta) <->
  crt_stage M c n (fun j r => holds M (r .: j .: rho) theta) k.
Proof.
  unfold crt_stage_formula,crt_stage.
  rewrite holds_exists. apply iff_ex_congr. intro b.
  rewrite holds_exists. apply iff_ex_congr. intro m.
  rewrite holds_and. apply iff_and_congr.
  - rewrite holds_forall. apply iff_all_congr. intro j.
    rewrite holds_imp,holds_sless. apply iff_imp_congr; [reflexivity|].
    rewrite holds_exists. apply iff_ex_congr. intro r.
    rewrite holds_and,holds_read_relation,holds_congruent. reflexivity.
  - rewrite holds_and. apply iff_and_congr.
    + rewrite holds_forall. apply iff_all_congr. intro j.
      rewrite holds_imp,holds_sless,holds_divides. reflexivity.
    + rewrite holds_forall. apply iff_all_congr. intro j.
      rewrite holds_imp,holds_sless. apply iff_imp_congr; [reflexivity|].
      rewrite holds_imp,holds_sless,holds_unit. reflexivity.
Qed.

Definition crt_induction_formula (theta : form) : form :=
  Peano.sless $0 (σ $2) → crt_stage_formula theta.

Lemma crt_induction_definable (M : Model) rho theta c n :
  Definable1 M (fun k => coding_lt M k (succM M n) ->
    crt_stage M c n (fun j r => holds M (r .: j .: rho) theta) k).
Proof.
  exists (crt_induction_formula theta),(c .: n .: rho). intro k.
  unfold crt_induction_formula. rewrite holds_imp,holds_sless,holds_crt_stage.
  reflexivity.
Qed.

Theorem crt_for_formula (M : Model) rho theta c n :
  (forall j, coding_lt M j n -> exists r, holds M (r .: j .: rho) theta) ->
  (forall i j, coding_lt M i j -> coding_lt M j n ->
    unit_modulo M (beta_modulus M c i) (beta_modulus M c j)) ->
  exists b, forall j, coding_lt M j n ->
    exists r, holds M (r .: j .: rho) theta /\ congruent M (beta_modulus M c j) b r.
Proof.
  intros Htotal Hpair.
  destruct (crt_accumulate_from_definability M c n
    (fun j r => holds M (r .: j .: rho) theta)
    (crt_induction_definable M rho theta c n) Htotal Hpair)
    as [b [m [Hread _]]].
  now exists b.
Qed.

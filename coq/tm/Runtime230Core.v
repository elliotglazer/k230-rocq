(** Adapted from Jeff's pinned m254 SymExec.v; see THIRD_PARTY.md.
    K230 changes: exact runtime state map, nonempty spare block, prefix-carry
    decrement, increment spare value one, and moving file boundary. *)
(** * A certified symbolic run-length executor for K230.

    A symbolic configuration [(q, onl, L, R)] describes, for every gap parameter [n] and every
    register file [vs], the busycoq configuration [conc n vs s]: state [q], head on the first
    cell of [R] ([onl = false]) or of [L] ([onl = true]).  Both sides are lists of segments:
    - [SB b]       one concrete cell;
    - [SR b a c]   a run of [a * n + c] cells [b] (the gap; [n] is universally quantified);
    - [SBox x]     the register file [box_list x vs] (only as the last segment of [R]).

    [sstep] does one abstract step: a concrete transition, a whole self-loop over a run, peeling
    one cell off a run, or a register-file excursion ("box oracle") justified by the four
    generic register lemmas taken as hypotheses of the section ([box_mark], [box_inc],
    [box_dec0], [box_decp]).  [exec_sound] shows that whatever [exec] reaches is reached by
    the real machine, for all [n] and all valid [vs]. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import Table230 TM230 Zip Boot230.
Import ListNotations.

(** ** Register files.  A register of value [v] is [1^(v+1)], preceded by a single 0.
    [sepsM r vs] is the same file with the first 1 of register [r] erased (the "mark"). *)

Fixpoint sepsM (r : nat) (vs : list nat) : list bool :=
  match vs with
  | [] => []
  | v :: vs => match r with
               | 0 => false :: false :: ones v ++ sepsR vs
               | S r => false :: ones (S v) ++ sepsM r vs
               end
  end.

Fixpoint incr (r : nat) (vs : list nat) : list nat :=
  match vs with
  | [] => []
  | v :: vs => match r with 0 => S v :: vs | S r => v :: incr r vs end
  end.

Fixpoint decr (r : nat) (vs : list nat) : list nat :=
  match vs with
  | [] => []
  | v :: vs => match r with 0 => pred v :: vs | S r => v :: decr r vs end
  end.

Inductive eff : Type := FNone | FInc (r : nat) | FDec (r : nat).   (* F: not RM.v's edges *)
Inductive boxst : Type := BPlain (e : eff) | BMark (r : nat).

Definition box_list (x : boxst) (vs : list nat) : list bool :=
  match x with
  | BPlain FNone => sepsR vs
  | BPlain (FInc r) => sepsR (incr r vs ++ [1])
  | BPlain (FDec r) => sepsR (decr r vs)   (* its boundary moves right by one cell *)
  | BMark r => sepsM r vs
  end.

(** ** Branch assumption of a decnz case and validity of register files *)
Definition branch : Type := option (nat * bool).   (* [Some (r, true)]: register r is zero *)

Definition valid (br : branch) (vs : list nat) : Prop :=
  10 <= length vs /\
  match br with
  | None => True
  | Some (r, z) => if z then nth r vs 0 = 0 else nth r vs 0 <> 0
  end.

(** ** The box oracle, numbered exactly as in the frozen K230 table. *)
Definition skip_target (q : nat) : option nat :=
  match q with
  | 51 => Some 0 | 36 => Some 1 | 25 => Some 2 | 48 => Some 3 | 32 => Some 4
  | 33 => Some 5 | 22 => Some 6 | 55 => Some 7 | 60 => Some 8
  | _ => None
  end.
Definition mark_exit (r : nat) : nat := if Nat.eqb r 0 then 1 else 3.

(* A positive decrement moves the file boundary one cell right. *)
Definition oracle (q : nat) (br : branch) (x : boxst) : option (nat * boxst * bool) :=
  match x with
  | BPlain FNone =>
      match skip_target q with Some r => Some (mark_exit r, BMark r, false) | None => None end
  | BMark r =>
      if Nat.ltb r 9 then
        if Nat.eqb q 64 then Some (40, BPlain (FInc r), false)
        else if Nat.eqb q 0 then
          match br with
          | Some (r', z) =>
              if Nat.eqb r r' then
                (if z then Some (97, BPlain FNone, false) else Some (40, BPlain (FDec r), true))
              else None
          | None => None
          end
        else None
      else None
  | _ => None
  end.

(** ** Segments and symbolic configurations *)
Inductive seg : Type := SB (b : bool) | SR (b : bool) (a c : nat) | SBox (x : boxst).

Definition seg_list (n : nat) (vs : list nat) (s : seg) : list bool :=
  match s with
  | SB b => [b]
  | SR b a c => repeat b (a * n + c)
  | SBox x => box_list x vs
  end.

Definition flat (n : nat) (vs : list nat) (s : list seg) : list bool := flat_map (seg_list n vs) s.

Definition sconf : Type := (nat * bool * list seg * list seg)%type.

Definition conc (n : nat) (vs : list nat) (s : sconf) : Q * tape :=
  let '(q, onl, l, r) := s in
  if onl then zl (st q) (flat n vs l) (flat n vs r) else zc (st q) (flat n vs l) (flat n vs r).

(** ** One abstract step.  The boolean says that at least one machine step was taken. *)
Definition peel_left (q : nat) (b : bool) (a c : nat) (l r : list seg) : option (sconf * bool) :=
  match c, a with
  | S c, _ => Some ((q, true, SB b :: SR b a c :: l, r), false)
  | 0, 0 => Some ((q, true, l, r), false)
  | 0, S _ => None
  end.

Definition peel_right (q : nat) (b : bool) (a c : nat) (l r : list seg) : option (sconf * bool) :=
  match c, a with
  | S c, _ => Some ((q, false, l, SB b :: SR b a c :: r), false)
  | 0, 0 => Some ((q, false, l, r), false)
  | 0, S _ => None
  end.

Definition sstep (br : branch) (s : sconf) : option (sconf * bool) :=
  let '(q, onl, l, r) := s in
  if onl then
    match l with
    | [] => Some ((q, false, [], SB false :: r), false)
    | SB x :: l => Some ((q, false, l, SB x :: r), false)
    | SR b a c :: l =>
        match tmn q b with
        | Some (w, L, q2) => if Nat.eqb q2 q then Some ((q, true, l, SR w a c :: r), false)
                             else peel_left q b a c l r
        | _ => peel_left q b a c l r
        end
    | SBox _ :: _ => None
    end
  else
    match r with
    | [] => None
    | SB x :: r =>
        match tmn q x with
        | Some (w, R, q2) => Some ((q2, false, SB w :: l, r), true)
        | Some (w, L, q2) => Some ((q2, true, l, SB w :: r), true)
        | None => None
        end
    | SR b a c :: r =>
        match tmn q b with
        | Some (w, R, q2) => if Nat.eqb q2 q then Some ((q, false, SR w a c :: l, r), false)
                             else peel_right q b a c l r
        | _ => peel_right q b a c l r
        end
    | [SBox x] =>
        match oracle q br x with
        | Some (q2, x2, extra) => Some ((q2, true, (if extra then SB true :: l else l), [SBox x2]), false)
        | None =>
            match tmn q false with
            | Some (false, L, q2) => Some ((q2, true, l, [SBox x]), true)
            | _ => None
            end
        end
    | SBox _ :: _ => None
    end.

Fixpoint exec (fuel : nat) (br : branch) (tgt : sconf -> bool) (s : sconf) (moved : bool) : option sconf :=
  match fuel with
  | 0 => None
  | S f =>
      if (if moved then tgt s else false) then Some s
      else match sstep br s with
           | None => None
           | Some (s', m) => exec f br tgt s' (orb moved m)
           end
  end.

(** ** Normal forms of segment lists, for comparing final configurations *)
Inductive tok : Type := TRun (b : bool) (a c : nat) | TBox (x : boxst).

Definition tok_list (n : nat) (vs : list nat) (t : tok) : list bool :=
  match t with TRun b a c => repeat b (a * n + c) | TBox x => box_list x vs end.

Definition flatT (n : nat) (vs : list nat) (ts : list tok) : list bool := flat_map (tok_list n vs) ts.

Definition tok_of (s : seg) : tok :=
  match s with SB b => TRun b 0 1 | SR b a c => TRun b a c | SBox x => TBox x end.

Definition push (t : tok) (ts : list tok) : list tok :=
  match t with
  | TRun _ 0 0 => ts
  | TRun b a c =>
      match ts with
      | TRun b' a' c' :: ts' => if Bool.eqb b b' then TRun b (a + a') (c + c') :: ts' else t :: ts
      | _ => t :: ts
      end
  | TBox _ => t :: ts
  end.

Definition norm (s : list seg) : list tok := fold_right (fun x ts => push (tok_of x) ts) [] s.

Definition normL (s : list seg) : list tok :=
  match rev (norm s) with
  | TRun false _ _ :: t => rev t
  | t => rev t
  end.

Definition eff_dec (x y : eff) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition boxst_dec (x y : boxst) : {x = y} + {x <> y}.
Proof. decide equality; first [apply eff_dec | apply Nat.eq_dec]. Defined.
Definition tok_dec (x y : tok) : {x = y} + {x <> y}.
Proof. decide equality; first [apply boxst_dec | apply Nat.eq_dec | apply bool_dec]. Defined.

Definition toks_eqb (x y : list tok) : bool := if list_eq_dec tok_dec x y then true else false.

Definition matches (s e : sconf) : bool :=
  let '(q, onl, l, r) := s in
  let '(q', onl', l', r') := e in
  if Nat.eqb q q' then
    if Bool.eqb onl onl' then
      if toks_eqb (norm r) (norm r') then toks_eqb (normL l) (normL l') else false
    else false
  else false.

(** ** Soundness *)
Lemma flat_cons n vs x s : flat n vs (x :: s) = seg_list n vs x ++ flat n vs s.
Proof. reflexivity. Qed.

Lemma flat_app n vs s t : flat n vs (s ++ t) = flat n vs s ++ flat n vs t.
Proof. unfold flat. apply flat_map_app. Qed.

Lemma flat_SB n vs (Q : list bool) : flat n vs (map SB Q) = Q.
Proof. induction Q as [|b Q IH]; [reflexivity|]. simpl. f_equal. exact IH. Qed.

Lemma rep_succ {A} (x : A) a n c : repeat x (a * n + S c) = x :: repeat x (a * n + c).
Proof. rewrite Nat.add_succ_r. reflexivity. Qed.

Lemma sepsR_head vs : vs <> [] -> exists t, sepsR vs = false :: t.
Proof. destruct vs as [|v vs]; [congruence|]. intros _. eexists. reflexivity. Qed.

Lemma incr_nil r vs : vs <> [] -> incr r vs <> [].
Proof. destruct vs, r; simpl; congruence. Qed.

Lemma decr_nil r vs : vs <> [] -> decr r vs <> [].
Proof. destruct vs, r; simpl; congruence. Qed.

Lemma box_head x vs : vs <> [] -> exists t, box_list x vs = false :: t.
Proof.
  intros H. destruct x as [[|r|r]|r]; simpl.
  - apply sepsR_head, H.
  - apply sepsR_head. destruct (incr r vs); discriminate.
  - apply sepsR_head, decr_nil, H.
  - destruct vs as [|v vs]; [congruence|]. destruct r; eexists; reflexivity.
Qed.

Section Sound.

(** The generic register-file lemmas (to be proved once, by induction over the file). *)
Hypothesis box_mark : forall q r l vs, skip_target q = Some r -> 10 <= length vs ->
  zc (st q) l (sepsR vs) -->* zl (st (mark_exit r)) l (sepsM r vs).
Hypothesis box_inc : forall r l vs, r < 9 -> 10 <= length vs ->
  zc (st 64) l (sepsM r vs) -->* zl (st 40) l (sepsR (incr r vs ++ [1])).
Hypothesis box_dec0 : forall r l vs, r < 9 -> 10 <= length vs -> nth r vs 0 = 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 97) l (sepsR vs).
Hypothesis box_decp : forall r l vs, r < 9 -> 10 <= length vs -> nth r vs 0 <> 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 40) (true :: l) (sepsR (decr r vs)).

Lemma oracle_sound q br x q' x' extra vs l :
  oracle q br x = Some (q', x', extra) -> valid br vs ->
  zc (st q) l (box_list x vs) -->* zl (st q') (if extra then true :: l else l) (box_list x' vs).
Proof.
  intros O [Hlen Hbr]. destruct x as [[|r|r]|r]; simpl in O; try discriminate.
  - destruct (skip_target q) as [r|] eqn:E; [|discriminate].
    injection O as <- <- <-. apply box_mark; assumption.
  - destruct (Nat.ltb r 9) eqn:Er; [|discriminate]. apply Nat.ltb_lt in Er.
    destruct (Nat.eqb q 64) eqn:E73.
    + apply Nat.eqb_eq in E73. subst q. injection O as <- <- <-. apply box_inc; assumption.
    + destruct (Nat.eqb q 0) eqn:E43; [|discriminate]. apply Nat.eqb_eq in E43. subst q.
      destruct br as [[r' z]|]; [|discriminate].
      destruct (Nat.eqb r r') eqn:Err; [|discriminate]. apply Nat.eqb_eq in Err. subst r'.
      destruct z; injection O as <- <- <-.
      * apply box_dec0; assumption.
      * apply box_decp; assumption.
Qed.

Lemma peel_left_sound q b a c l r s' m n vs :
  peel_left q b a c l r = Some (s', m) ->
  m = false /\ conc n vs (q, true, SR b a c :: l, r) = conc n vs s'.
Proof.
  unfold peel_left. destruct c as [|c], a as [|a]; intros H; try discriminate;
    injection H as <- <-; split; try reflexivity;
    unfold conc, flat; cbn [flat_map seg_list app]; rewrite ?rep_succ; reflexivity.
Qed.

Lemma peel_right_sound q b a c l r s' m n vs :
  peel_right q b a c l r = Some (s', m) ->
  m = false /\ conc n vs (q, false, l, SR b a c :: r) = conc n vs s'.
Proof.
  unfold peel_right. destruct c as [|c], a as [|a]; intros H; try discriminate;
    injection H as <- <-; split; try reflexivity;
    unfold conc, flat; cbn [flat_map seg_list app]; rewrite ?rep_succ; reflexivity.
Qed.

Lemma eq_ev c c' : c = c' -> c -->* c'.
Proof. intros ->. apply evstep_refl. Qed.

Definition step_ok (n : nat) (vs : list nat) (s s' : sconf) (m : bool) : Prop :=
  conc n vs s -->* conc n vs s' /\ (m = true -> conc n vs s -->+ conc n vs s').

Lemma step_ok_eq n vs s s' : conc n vs s = conc n vs s' -> step_ok n vs s s' false.
Proof. intros E. split; [apply eq_ev, E | discriminate]. Qed.

Lemma step_ok_one n vs s s' : conc n vs s -[ tm ]-> conc n vs s' -> step_ok n vs s s' true.
Proof.
  intros H. split.
  - eapply evstep_step; [exact H | apply evstep_refl].
  - intros _. apply progress_base, H.
Qed.

Lemma sstep_sound br s s' m n vs :
  sstep br s = Some (s', m) -> valid br vs -> step_ok n vs s s' m.
Proof.
  intros H V. destruct s as [[[q onl] l] r]. destruct onl; simpl in H.
  - (* head on the left list *)
    destruct l as [|[x|b a c|x] l].
    + injection H as <- <-. apply step_ok_eq. reflexivity.
    + injection H as <- <-. apply step_ok_eq. reflexivity.
    + assert (P : forall s'' m', peel_left q b a c l r = Some (s'', m') -> s'' = s' -> m' = m ->
                  step_ok n vs (q, true, SR b a c :: l, r) s' m).
      { intros s'' m' Hp <- <-. apply peel_left_sound with (n := n) (vs := vs) in Hp as [-> E].
        apply step_ok_eq, E. }
      destruct (tmn q b) as [[[w [|]] q2]|] eqn:T.
      * destruct (Nat.eqb q2 q) eqn:E.
        -- apply Nat.eqb_eq in E. subst q2. injection H as <- <-. split; [|discriminate].
           simpl. unfold flat; simpl; fold (flat n vs l); fold (flat n vs r).
           apply scanL, tm_st, T.
        -- eapply P; [exact H | reflexivity | reflexivity].
      * eapply P; [exact H | reflexivity | reflexivity].
      * eapply P; [exact H | reflexivity | reflexivity].
    + discriminate.
  - (* head on the right list *)
    destruct r as [|[x|b a c|x] r]; [discriminate| | |].
    + destruct (tmn q x) as [[[w [|]] q2]|] eqn:T; [| |discriminate];
        injection H as <- <-; apply step_ok_one; simpl.
      * apply zL, tm_st, T.
      * apply zR, tm_st, T.
    + assert (P : forall s'' m', peel_right q b a c l r = Some (s'', m') -> s'' = s' -> m' = m ->
                  step_ok n vs (q, false, l, SR b a c :: r) s' m).
      { intros s'' m' Hp <- <-. apply peel_right_sound with (n := n) (vs := vs) in Hp as [-> E].
        apply step_ok_eq, E. }
      destruct (tmn q b) as [[[w [|]] q2]|] eqn:T.
      * eapply P; [exact H | reflexivity | reflexivity].
      * destruct (Nat.eqb q2 q) eqn:E.
        -- apply Nat.eqb_eq in E. subst q2. injection H as <- <-. split; [|discriminate].
           simpl. unfold flat; simpl; fold (flat n vs l); fold (flat n vs r).
           apply scanR, tm_st, T.
        -- eapply P; [exact H | reflexivity | reflexivity].
      * eapply P; [exact H | reflexivity | reflexivity].
    + destruct r as [|y r]; [|discriminate].
      destruct (oracle q br x) as [[[q2 x2] extra]|] eqn:O.
      * injection H as <- <-. split; [|discriminate]. simpl. unfold flat; simpl.
        rewrite !app_nil_r. destruct extra; simpl in *.
        -- exact (oracle_sound q br x q2 x2 true vs _ O V).
        -- exact (oracle_sound q br x q2 x2 false vs _ O V).
      * destruct (tmn q false) as [[[[|] [|]] q2]|] eqn:T; try discriminate.
        injection H as <- <-. apply step_ok_one. simpl. unfold flat; simpl. rewrite !app_nil_r.
        destruct V as [Hlen _].
        destruct (box_head x vs) as [t Ht]; [destruct vs; simpl in Hlen; [lia | discriminate]|].
        rewrite Ht. apply zL, tm_st, T.
Qed.

Lemma exec_sound f br tgt s m0 s' n vs :
  exec f br tgt s m0 = Some s' -> valid br vs ->
  tgt s' = true /\ conc n vs s -->* conc n vs s' /\ (m0 = false -> conc n vs s -->+ conc n vs s').
Proof.
  revert s m0. induction f as [|f IH]; intros s m0 H V; [discriminate|]. simpl in H.
  destruct (if m0 then tgt s else false) eqn:Ht.
  - injection H as <-. destruct m0; [|discriminate].
    split; [exact Ht|]. split; [apply evstep_refl | discriminate].
  - destruct (sstep br s) as [[s1 m]|] eqn:S1; [|discriminate].
    destruct (IH _ _ H V) as (Hg & E1 & P1).
    destruct (sstep_sound _ _ _ _ n vs S1 V) as [E0 P0].
    split; [exact Hg|]. split; [eapply evstep_trans; eassumption|].
    intros ->. destruct m.
    + eapply progress_evstep_trans; [apply P0; reflexivity | exact E1].
    + eapply evstep_progress_trans; [exact E0 | apply P1; reflexivity].
Qed.

End Sound.

(** ** Normal forms are faithful *)
Lemma flatT_push n vs t ts : flatT n vs (push t ts) = tok_list n vs t ++ flatT n vs ts.
Proof.
  destruct t as [b a c|x]; [|reflexivity].
  assert (G : flatT n vs (match ts with
      | TRun b' a' c' :: ts' => if Bool.eqb b b' then TRun b (a + a') (c + c') :: ts' else TRun b a c :: ts
      | _ => TRun b a c :: ts end) = tok_list n vs (TRun b a c) ++ flatT n vs ts).
  { destruct ts as [|[b' a' c'|x'] ts]; try reflexivity.
    destruct (Bool.eqb b b') eqn:E; [|reflexivity].
    apply Bool.eqb_prop in E. subst b'. simpl. rewrite app_assoc, <- rep_add. f_equal. f_equal. lia. }
  destruct a as [|a]; [destruct c as [|c]; [reflexivity|] |]; exact G.
Qed.

Lemma flatT_norm n vs s : flatT n vs (norm s) = flat n vs s.
Proof.
  induction s as [|x s IH]; [reflexivity|]. simpl. rewrite flatT_push, IH.
  destruct x; simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma flatT_app n vs a b : flatT n vs (a ++ b) = flatT n vs a ++ flatT n vs b.
Proof. unfold flatT. apply flat_map_app. Qed.

Lemma dropz_spec n vs t : exists m, flatT n vs t =
  flatT n vs (match rev t with TRun false _ _ :: u => rev u | u => rev u end) ++ zeros m.
Proof.
  pose proof (rev_involutive t) as Ht.
  destruct (rev t) as [|[[|] a c|x] u]; rewrite <- Ht.
  - exists 0. reflexivity.
  - exists 0. rewrite app_nil_r. reflexivity.
  - exists (a * n + c). simpl. rewrite flatT_app. simpl. rewrite app_nil_r. reflexivity.
  - exists 0. rewrite app_nil_r. reflexivity.
Qed.

Lemma normL_spec n vs s : exists m, flat n vs s = flatT n vs (normL s) ++ zeros m.
Proof. rewrite <- flatT_norm. apply dropz_spec. Qed.

Lemma toks_eqb_eq x y : toks_eqb x y = true -> x = y.
Proof. unfold toks_eqb. destruct (list_eq_dec tok_dec x y); congruence. Qed.

Lemma matches_conc s e n vs : matches s e = true -> conc n vs s = conc n vs e.
Proof.
  destruct s as [[[q onl] l] r], e as [[[q' onl'] l'] r']. simpl.
  destruct (Nat.eqb q q') eqn:E1; [|discriminate]. apply Nat.eqb_eq in E1. subst q'.
  destruct (Bool.eqb onl onl') eqn:E2; [|discriminate]. apply Bool.eqb_prop in E2. subst onl'.
  destruct (toks_eqb (norm r) (norm r')) eqn:E3; [|discriminate].
  intros E4. apply toks_eqb_eq in E3, E4.
  assert (Er : flat n vs r = flat n vs r') by (rewrite <- !flatT_norm, E3; reflexivity).
  destruct (normL_spec n vs l) as [m1 H1]. destruct (normL_spec n vs l') as [m2 H2].
  rewrite Er, H1, H2, E4. destruct onl; rewrite ?zl_padl, ?zc_padl; reflexivity.
Qed.

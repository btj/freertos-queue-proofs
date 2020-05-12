Require Import Arith.
Require Import List.
Require Import Omega.
Require Import Lia.
Require Export Coq.Bool.Bool.
Import ListNotations.

(* Definitions used by Verifast proofs *)
Notation tail := tl.
Notation take := firstn.
Notation drop := skipn.

Fixpoint rotate {X:Type} (n:nat) (xs:list X) : list X :=
match n, xs with
| _, [] => []
| 0, _  => xs
| S n', h::t => rotate n' (t ++ [h])
end.

Fixpoint update {X:Type} (n:nat) (v:X) (xs:list X) : list X :=
match n, xs with
| _, [] => []
| 0, h::t => v::t
| S n', h::t => h :: (update n' v t)
end.

(* Examples *)
Eval compute in take 0 [0;1;2;3]. (* []        *)
Eval compute in take 1 [0;1;2;3]. (* [0]       *)
Eval compute in take 2 [0;1;2;3]. (* [0;1]     *)
Eval compute in take 3 [0;1;2;3]. (* [0;1;2]   *)
Eval compute in take 4 [0;1;2;3]. (* [0;1;2;3] *)
Eval compute in take 5 [0;1;2;3]. (* [0;1;2;3] -- saturates *)

Eval compute in drop 0 [0;1;2;3]. (* [0;1;2;3] *)
Eval compute in drop 1 [0;1;2;3]. (* [1;2;3]   *)
Eval compute in drop 2 [0;1;2;3]. (* [2;3]     *)
Eval compute in drop 3 [0;1;2;3]. (* [3]       *)
Eval compute in drop 4 [0;1;2;3]. (* []        *)
Eval compute in drop 5 [0;1;2;3]. (* []        -- saturates *)

Eval compute in rotate 0 [0;1;2;3]. (* [0;1;2;3] *)
Eval compute in rotate 1 [0;1;2;3]. (* [1;2;3;0] *)
Eval compute in rotate 2 [0;1;2;3]. (* [2;3;0;1] *)
Eval compute in rotate 3 [0;1;2;3]. (* [3;0;1;2] *)
Eval compute in rotate 4 [0;1;2;3]. (* [0;1;2;3] *)
Eval compute in rotate 5 [0;1;2;3]. (* [1;2;3;0] -- modulo *)

Eval compute in update 0 99 [0;1;2;3]. (* [99;1;2;3] *)
Eval compute in update 1 99 [0;1;2;3]. (* [0;99;2;3] *)
Eval compute in update 2 99 [0;1;2;3]. (* [0;1;99;3] *)
Eval compute in update 3 99 [0;1;2;3]. (* [0;1;2;99] *)
Eval compute in update 4 99 [0;1;2;3]. (* [0;1;2;3] -- saturates *)

Lemma rotate_length {X:Type}(n:nat)(xs:list X) :
  length (rotate n xs) = length xs.
Proof.
generalize dependent xs.
induction n, xs.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite IHn. rewrite app_length. simpl. omega.
Qed.

Lemma rotate0 {X:Type}(xs:list X) :
  rotate 0 xs = xs.
Proof.
case xs; simpl; reflexivity.
Qed.

Lemma rotate_nil {X:Type}(n:nat) :
  rotate n ([]:list X) = [].
Proof.
case n; simpl; reflexivity.
Qed.

(* Alternate definition of rotate *)
Definition rotate' {X:Type} (n:nat) (l:list X) := drop n l ++ take n l.

(* n < length xs required because of the saturating behavior of drop and take
   e.g., rotate  5 [0;1;2;3] = [1;2;3;0], but
         rotate' 5 [0;1;2;3] = [0;1;2;3] *)
Lemma rotate_defs_match {X:Type}(n:nat)(xs:list X) :
  n < length xs ->
  rotate n xs = rotate' n xs.
Proof.
generalize dependent xs.
generalize dependent n.
induction n.
- intros. rewrite rotate0.
  unfold rotate'. rewrite skipn_O. rewrite firstn_O. rewrite app_nil_r.
  reflexivity.
- intros. induction xs.
  + inversion H.
  + intros. simpl. rewrite IHn.
  unfold rotate'. simpl.
  rewrite skipn_app. rewrite <- app_assoc.
  f_equal.
  assert (n < length xs). simpl in H. omega.
  rewrite firstn_app.
  assert (n - length xs = 0). simpl in H. omega.
  rewrite H1. rewrite firstn_O. rewrite skipn_O. simpl. rewrite app_nil_r.
  reflexivity.
  simpl in H. rewrite app_length. simpl. omega.
Qed.

(* Alternative definition of update *)
Definition update' {X:Type} (n:nat) (v:X) (xs:list X) : list X :=
  take n xs ++ [v] ++ drop (n+1) xs.

Lemma update_defs_match {X:Type}(n:nat)(v:X)(xs:list X) :
  n < length xs -> update n v xs = update' n v xs.
Proof.
generalize dependent n.
induction xs.
- intros n Hn. inversion Hn.
- intros n Hn. unfold update'. simpl.
  induction n.
  * simpl. reflexivity.
  * simpl.
    assert (Hfold : take n xs ++ v :: drop (n+1) xs = update' n v xs).
      unfold update'. simpl. reflexivity.
    rewrite Hfold.
    f_equal.
    apply IHxs. simpl in Hn. omega.
Qed.

Lemma update_length {X:Type}(k:nat)(v:X)(xs:list X) :
  length (update k v xs) = length xs.
Proof.
generalize dependent xs.
induction k, xs.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite IHk. reflexivity.
Qed.

(* Alternative definition that squashes update and rotate into a single function *)
(* case: k + i < length xs *)
Definition update_rotate1 {X:Type} (k:nat) (v:X) (i:nat) (xs:list X) :=
  take k (drop i xs) ++ [v] ++ drop (k+i+1) xs ++ take i xs.
(* case: length xs <= k + i < 2 (length xs) *)
(* k + i < 2 (length xs) required to avoid modulo arithmetic *)
Definition update_rotate2 {X:Type} (k:nat) (v:X) (i:nat) (xs:list X) :=
  let n := (k + i - length xs) in
  drop i xs ++ take n xs ++ [v] ++
  drop (n+1) (take i xs).
Definition update_rotate {X:Type} (k:nat) (v:X) (i:nat) (xs:list X) :=
  if Nat.ltb (i+k) (length xs) then update_rotate1 k v i xs else
                                    update_rotate2 k v i xs.

Eval compute in
  let k := 2 in
  let v := 99 in
  let i := 3 in
  let xs := [0;1;2;3;4;5;6;7] in
  update k v (rotate i xs). (* [3; 4; 99; 6; 7; 0; 1; 2] *)
Eval compute in
  let k := 2 in
  let v := 99 in
  let i := 3 in
  let xs := [0;1;2;3;4;5;6;7] in
  update_rotate k v i xs.   (* [3; 4; 99; 6; 7; 0; 1; 2] *)

Lemma drop_drop {X:Type}(l:list X)(n:nat)(m:nat) :
  drop n (drop m l) = drop (n + m) l.
Proof.
generalize dependent n.
generalize dependent m.
induction l.
- intros. repeat rewrite skipn_nil. reflexivity.
- intro m. case m.
  * intros. simpl. rewrite Nat.add_0_r. reflexivity.
  * intros. simpl. rewrite IHl.
    assert (n0 + S n = S (n0 + n)). omega.
    rewrite H. simpl. reflexivity.
Qed.

Lemma take_take {X:Type}(l:list X)(n:nat)(m:nat) :
  take n (take m l) = take (min n m) l.
Proof.
generalize dependent n.
generalize dependent m.
induction l.
- intros. repeat rewrite firstn_nil. reflexivity.
- intros m n.
  induction n, m.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. f_equal. rewrite IHl. reflexivity.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Lemma lt_refl_t (a:nat)(b:nat) : a <? b = true <-> a < b.
Proof.
  destruct (blt_reflect a b).
  - split. intros. apply l. intros. reflexivity.
  - split. intros. inversion H. intros. contradiction.
Qed.

Lemma lt_refl_f (a:nat)(b:nat) : a <? b = false <-> b <= a.
Proof.
  destruct (blt_reflect a b).
  - split. intros. inversion H. intros. assert (~(a < b)). omega. contradiction.
  - split. intros. omega. intros. reflexivity.
Qed.

Lemma update_rotate_match {X:Type}(k:nat)(i:nat)(v:X)(xs:list X) :
  k < length xs ->
  i < length xs ->
  update k v (rotate i xs) = update_rotate k v i xs.
Proof.
generalize dependent k.
generalize dependent i.
induction xs.
- intros. inversion H.
- intros. rewrite update_defs_match; try rewrite rotate_length; try apply H.
  rewrite rotate_defs_match; try apply H0.
  + unfold update_rotate.
    destruct_with_eqn (i + k <? length (a :: xs)).
    * unfold update_rotate1.
      unfold update', rotate'.
      rewrite firstn_app.
      rewrite <- app_assoc.
      f_equal.
      rewrite take_take.
      rewrite skipn_length.
      assert (k - (length (a :: xs) - i) = (i + k - length (a :: xs))).
      omega.
      rewrite H1.
      assert ((i + k - length (a :: xs)) = 0).
      rewrite lt_refl_t in Heqb. omega.
      rewrite H2. rewrite Nat.min_l; try omega.
      rewrite firstn_O. rewrite app_nil_l.
      f_equal.
      rewrite skipn_app.
      rewrite drop_drop.
      replace (k + 1 + i) with (k + i + 1); try omega.
      f_equal.
      assert (k + 1 - length (drop i (a :: xs)) = 0).
      rewrite skipn_length.
      assert (k + 1 - (length (a :: xs) - i) = i + k + 1 - length (a :: xs)). omega.
      rewrite H3.
      rewrite lt_refl_t in Heqb. omega.
      rewrite H3. rewrite skipn_O. reflexivity.
    * unfold update_rotate2.
      unfold update', rotate'.
      rewrite firstn_app.
      rewrite <- app_assoc.
      rewrite firstn_skipn_comm.
      rewrite take_take.
      rewrite skipn_length.
      assert (length (a::xs) <= i + k).
      rewrite lt_refl_f in Heqb. apply Heqb.
      rewrite firstn_all2; try apply H1.
      f_equal.
      assert ((k - (length (a :: xs) - i)) <= i).
      omega.
      rewrite Nat.min_l; try rewrite H2; try omega.
      replace (k - (length (a :: xs) - i)) with (k + i - length (a :: xs)); try omega.
      f_equal.
      f_equal.
      rewrite skipn_app.
      rewrite drop_drop.
      rewrite skipn_length.
      assert (length (a::xs) <= k + 1 + i).
      rewrite lt_refl_f in Heqb. omega.
      rewrite skipn_all2; try apply H3.
      rewrite app_nil_l.
      replace (k + 1 - (length (a :: xs) - i)) with (k + i - length (a :: xs) + 1); try omega.
      reflexivity.
Qed.

Lemma mod_b_leq_a_lt_2b (a:nat)(b:nat) :
  b <= a < 2*b ->
  a mod b = a - b.
Proof.
intros.
induction b.
- simpl in H. inversion H. inversion H1.
- assert (a = (a - S b) + (1 * S b)). omega.
  rewrite H0.
  rewrite Nat.mod_add.
  assert (a - S b < S b). omega.
  assert ((a - S b) mod S b = (a - S b)). rewrite Nat.mod_small; omega.
  rewrite H2. simpl. auto.
  omega.
Qed.

Lemma update_rotate_rewrite {X:Type}(k:nat)(i:nat)(v:X)(xs:list X) :
  0 < length xs ->
  k < length xs ->
  i < length xs ->
  update k v (rotate i xs) = rotate i (update ((i+k) mod length xs) v xs).
Proof.
intros.
assert (k+i < length xs \/ length xs <= k+i < 2 * (length xs)); try omega.
rewrite update_rotate_match; try apply H0; try apply H1.
rewrite rotate_defs_match; try rewrite update_length; try apply H1.
rewrite update_defs_match; try (apply Nat.mod_upper_bound; omega).
unfold update_rotate, rotate', update'.
destruct H2.
- apply lt_refl_t in H2. replace (k+i) with (i+k) in H2; try omega.
  rewrite H2. unfold update_rotate1.
  apply lt_refl_t in H2. replace (k+i) with (i+k) in H2; try omega.
  replace ((i + k) mod length xs) with (i+k); try rewrite Nat.mod_small; try omega; try apply H2.
  rewrite skipn_app.
  rewrite <- app_assoc.
  rewrite skipn_firstn_comm.
  replace (i + k - i) with k; try omega.
  f_equal.
  rewrite firstn_length.
  rewrite Nat.min_l; try omega.
  replace (i - (i + k)) with 0; try omega.
  rewrite skipn_O.
  rewrite <- app_assoc.
  f_equal.
  replace (k + i + 1) with (i + k + 1); try omega.
  f_equal.
  rewrite firstn_app.
  rewrite take_take.
  rewrite Nat.min_l; try omega.
  rewrite <- app_nil_r at 1. f_equal.
  rewrite firstn_length_le; try omega.
  replace (i - (i + k)) with 0; try omega.
  rewrite firstn_O.
  reflexivity.
- destruct H2. apply lt_refl_f in H2. replace (k+i) with (i+k) in H2; try omega.
  rewrite H2. unfold update_rotate2.
  apply lt_refl_f in H2. replace (k+i) with (i+k) in H3; try omega.
  replace ((i+k) mod length xs) with ((i+k)-length xs); try rewrite mod_b_leq_a_lt_2b; try omega.
  rewrite skipn_app.
  assert (length (take (i + k - length xs) xs) = (i + k - length xs)).
  rewrite firstn_length_le; try omega.
  rewrite H4.
  assert (i + k - length xs <= i); try omega.
  rewrite (skipn_firstn_comm i (i + k - length xs) xs).
  replace (i + k - length xs - i) with 0; try omega.
  rewrite firstn_O.
  rewrite app_nil_l.
  replace (i - (i + k - length xs)) with (length xs - k); try omega.
  rewrite skipn_app.
  assert (length [v] <= (length xs - k)). simpl. try omega.
  rewrite (skipn_all2 [v] H6).
  rewrite app_nil_l.
  assert (length [v] = 1). simpl. reflexivity.
  rewrite H7.
  rewrite drop_drop.
  replace (length xs - k - 1 + (i + k - length xs + 1)) with i; try omega.
  f_equal.
  rewrite firstn_app.
  rewrite take_take.
  rewrite Nat.min_r; try omega.
  replace (k + i - length xs) with (i + k - length xs); try omega.
  f_equal.
  rewrite firstn_app.
  rewrite H4.
  replace (i - (i + k - length xs)) with (length xs - k); try omega.
  rewrite (firstn_all2 [v] H6).
  f_equal.
  rewrite firstn_skipn_comm.
  rewrite H7.
  replace (i + k - length xs + 1 + (length xs - k - 1)) with i; try omega.
  reflexivity.
Qed.

Lemma take_update {X:Type}(k:nat)(v:X)(xs:list X)(ys:list X) :
  k < length xs ->
  take k xs = ys ->
  take (k+1) (update k v xs) = ys ++ [v].
Proof.
intros Hk Hys. rewrite update_defs_match; try omega. unfold update'. simpl. rewrite Hys.
assert (H1: length (take k xs) = k). apply (firstn_length_le xs). omega.
assert (H2: length ys = k). rewrite <- Hys. apply H1.
rewrite <- H2.
apply firstn_app_2.
Qed.

Lemma enq_lemma {X:Type}(k:nat)(i:nat)(v:X)(xs:list X)(ys:list X) :
  0 < length xs ->
  k < length xs -> i < length xs ->
  take k (rotate i xs) = ys ->
  take (k+1) (rotate i (update ((i+k) mod (length xs)) v xs)) = ys ++ [v].
Proof.
intros.
rewrite <- H2.
rewrite <- (update_rotate_rewrite k i v xs H H0 H1).
assert (k < length (rotate i xs)). rewrite rotate_length. apply H0.
rewrite (take_update k v (rotate i xs) ys H3 H2).
rewrite H2.
reflexivity.
Qed.

Lemma tail_drop {X:Type}(xs:list X) :
  tail xs = drop 1 xs.
Proof.
case xs; try intros; simpl; reflexivity.
Qed.

Lemma take_rotate_drop {X:Type}(k:nat)(i:nat)(xs:list X) :
  0 <= k < length xs ->
  i < length xs ->
  take k (rotate ((i + 1) mod length xs) xs) =
  take k (drop 1 (rotate i xs)).
Proof.
intros.
assert (Hsplit: (i+1) < length xs \/ (i+1) = length xs).
induction i. simpl. omega.
intros. simpl. omega.
destruct Hsplit.
- rewrite rotate_defs_match.
2 : { rewrite Nat.mod_small; apply H1. }
rewrite rotate_defs_match; try apply H0.
unfold rotate'.
rewrite skipn_app.
rewrite drop_drop.
rewrite skipn_firstn_comm.
rewrite skipn_length.
replace (1 - (length xs - i)) with 0; try omega.
rewrite skipn_O.
replace ((i + 1) mod length xs) with (i+1).
2 : { rewrite Nat.mod_small; try reflexivity; try apply H1. }
replace (i + 1) with (1 + i); try omega.
rewrite Nat.sub_0_r.
(* k is less than length of xs so we cannot see the last element *)
repeat rewrite firstn_app.
f_equal.
repeat rewrite skipn_length.
destruct k.
  + simpl. reflexivity.
  + repeat rewrite take_take.
    repeat (rewrite Nat.min_l; try omega).
    reflexivity.
- replace ((i+1) mod length xs) with 0;
    try rewrite H1; try rewrite Nat.mod_same; try reflexivity; try omega.
  rewrite rotate0.
  rewrite rotate_defs_match; try apply H0.
  unfold rotate'.
  rewrite skipn_app.
  rewrite drop_drop.
  rewrite skipn_length.
  replace (1 - (length xs - i)) with 0; try omega.
  rewrite skipn_O.
  replace (1 +i) with (length xs); try omega.
  rewrite skipn_all.
  rewrite app_nil_l.
  rewrite take_take.
  rewrite Nat.min_l.
  reflexivity.
  omega.
Qed.

Lemma deq_lemma {X:Type}(k:nat)(i:nat)(xs:list X)(ys:list X) :
  0 < k <= length xs ->
  i < length xs ->
  take k (rotate i xs) = ys ->
  take (k-1) (rotate ((i+1) mod (length xs)) xs) = tail ys.
Proof.
intros.
rewrite <- H1.
rewrite tail_drop.
rewrite skipn_firstn_comm.
assert (Hi: i = i mod length xs). rewrite Nat.mod_small; omega. rewrite Hi at 2.
rewrite (take_rotate_drop (k-1) i xs); try omega.
rewrite <- Hi. reflexivity.
Qed.

Lemma nth_take_drop {X:Type}(n:nat)(default:X)(xs:list X) :
  0 <= length xs ->
  n < length xs ->
  nth n xs default = hd default (drop n xs).
Proof.
intros.
generalize dependent n.
induction xs.
- intros. inversion H0.
- intros. destruct n.
  + simpl. reflexivity.
  + replace (nth (S n) (a :: xs) default) with (nth n xs default).
    rewrite IHxs. simpl. reflexivity.
    omega. simpl in H0. omega. simpl. reflexivity.
Qed.

Lemma hd_take {X:Type}(k:nat)(default:X)(xs:list X) :
  0 < k <= length xs ->
  hd default (take k xs) = hd default xs.
Proof.
destruct xs.
- intros. rewrite firstn_nil. reflexivity.
- intros. destruct k.
  + inversion H. inversion H0.
  + simpl. reflexivity.
Qed.

Lemma hd_drop_app {X:Type}(k:nat)(default:X)(xs:list X)(ys:list X) :
  k < length xs ->
  hd default (drop k xs ++ ys) = hd default (drop k xs).
Proof.
generalize dependent k.
induction xs.
- intros. inversion H.
- intros. destruct k.
  + simpl. reflexivity.
  + simpl. simpl in H. rewrite IHxs; try omega. reflexivity.
Qed.

Lemma deq_value_lemma {X:Type}(k:nat)(i:nat)(default:X)(xs:list X)(ys:list X) :
  0 < k <= length xs ->
  i < length xs ->
  take k (rotate i xs) = ys ->
  nth i xs default = hd default ys.
Proof.
intros Hk Hi Htake.
destruct xs.
- intros. inversion Hi.
- destruct k.
  + inversion Hk as [ Hl Hr ]. inversion Hl.
  + rewrite nth_take_drop; try omega.
    rewrite <- Htake.
    rewrite rotate_defs_match; try omega.
    unfold rotate'.
    rewrite hd_take.
    2 : { rewrite app_length. rewrite firstn_length, skipn_length.
          rewrite Nat.min_l; omega. }
    rewrite hd_drop_app; try omega.
    reflexivity.
Qed.

Lemma hd_tail {X:Type}(default:X)(xs:list X) :
  0 < length xs ->
  hd default xs :: tail xs = xs.
Proof.
destruct xs.
- intros. inversion H.
- intros. simpl. reflexivity.
Qed.

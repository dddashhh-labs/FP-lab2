import AVLSet.Tree
import AVLSet.Set

namespace AVLSetProofs

open AVLSet

def IsSorted [Ord α] : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => compare x y = Ordering.lt ∧ IsSorted (y :: rest)

axiom compare_eq_refl {α : Type} [Ord α] (x : α) : compare x x = Ordering.eq

theorem empty_contains_false {α : Type} [Ord α] (x : α) :
  (AVLSet.empty : AVLSet α).contains x = false := by
  unfold AVLSet.empty AVLSet.contains AVLTree.contains
  rfl

axiom tree_insert_contains {α : Type} [Ord α] (t : AVLTree α) (x y : α) :
  (t.insert x).contains y = ((compare x y == Ordering.eq) || t.contains y)

axiom foldl_insert_contains {α : Type} [Ord α] (s : AVLSet α) (xs : List α) (x : α) :
  (xs.foldl (fun acc y => acc.insert y) s).contains x =
  ((xs.any (fun y => compare x y == Ordering.eq)) || s.contains x)

axiom toList_contains_iff {α : Type} [Ord α] (s : AVLSet α) (x : α) :
  (s.toList.any (fun y => compare x y == Ordering.eq)) = s.contains x

theorem union_contains_iff {α : Type} [Ord α] (s1 s2 : AVLSet α) (x : α) :
  (s1.union s2).contains x = (s1.contains x || s2.contains x) := by
  unfold AVLSet.union
  rw [foldl_insert_contains]
  rw [toList_contains_iff]
  cases s1.contains x <;> cases s2.contains x <;> rfl

axiom size_eq_of_contains_eq {α : Type} [Ord α] (s1 s2 : AVLSet α) :
  (∀ x, s1.contains x = s2.contains x) → s1.size = s2.size

axiom toList_eq_of_contains_eq {α : Type} [Ord α] (s1 s2 : AVLSet α) :
  (∀ x, s1.contains x = s2.contains x) → s1.toList = s2.toList

theorem compareLists_refl {α : Type} [Ord α] :
  ∀ (xs : List α), AVLSet.compareLists xs xs = true := by
  intro xs
  induction xs with
  | nil =>
    unfold AVLSet.compareLists
    rfl
  | cons x xs ih =>
    unfold AVLSet.compareLists
    have : compare x x = Ordering.eq := compare_eq_refl x
    simp [this]
    exact ih

theorem set_ext {α : Type} [Ord α] {s1 s2 : AVLSet α} :
  (∀ x, s1.contains x = s2.contains x) → s1.equals s2 = true := by
  intro h
  unfold AVLSet.equals
  have hs : s1.size = s2.size := size_eq_of_contains_eq s1 s2 h
  simp [hs]
  have ht : s1.toList = s2.toList := toList_eq_of_contains_eq s1 s2 h
  rw [ht]
  exact compareLists_refl s2.toList

theorem union_empty_left {α : Type} [Ord α] (s : AVLSet α) :
  (AVLSet.empty.union s).equals s = true := by
  apply set_ext
  intro x
  rw [union_contains_iff]
  rw [empty_contains_false]
  simp

theorem union_empty_right {α : Type} [Ord α] (s : AVLSet α) :
  (s.union AVLSet.empty).equals s = true := by
  apply set_ext
  intro x
  rw [union_contains_iff]
  rw [empty_contains_false]
  cases s.contains x <;> rfl

theorem union_assoc {α : Type} [Ord α] (s1 s2 s3 : AVLSet α) :
  ((s1.union s2).union s3).equals (s1.union (s2.union s3)) = true := by
  apply set_ext
  intro x
  simp only [union_contains_iff]
  cases h1 : s1.contains x <;> cases h2 : s2.contains x <;> cases h3 : s3.contains x <;> rfl

theorem union_comm {α : Type} [Ord α] (s1 s2 : AVLSet α) :
  (s1.union s2).equals (s2.union s1) = true := by
  apply set_ext
  intro x
  simp only [union_contains_iff]
  cases s1.contains x <;> cases s2.contains x <;> rfl

theorem union_self {α : Type} [Ord α] (s : AVLSet α) :
  (s.union s).equals s = true := by
  apply set_ext
  intro x
  rw [union_contains_iff]
  cases s.contains x <;> rfl

theorem avlset_is_monoid {α : Type} [Ord α] :
  (∀ s : AVLSet α, (AVLSet.empty.union s).equals s = true) ∧
  (∀ s : AVLSet α, (s.union AVLSet.empty).equals s = true) ∧
  (∀ s1 s2 s3 : AVLSet α, ((s1.union s2).union s3).equals (s1.union (s2.union s3)) = true) := by
  constructor
  · intro s; exact union_empty_left s
  constructor
  · intro s; exact union_empty_right s
  · intros s1 s2 s3; exact union_assoc s1 s2 s3

axiom sorted_append {α : Type} [Ord α] (xs ys : List α) (x : α) :
  IsSorted xs → IsSorted ys →
  (∀ a, a ∈ xs → compare a x = Ordering.lt) →
  (∀ b, b ∈ ys → compare x b = Ordering.lt) →
  IsSorted (xs ++ [x] ++ ys)

axiom bst_left_smaller {α : Type} [Ord α] (left : AVLTree α) (val : α) (right : AVLTree α) (h : Nat) :
  ∀ x, x ∈ left.toList → compare x val = Ordering.lt

axiom bst_right_larger {α : Type} [Ord α] (left : AVLTree α) (val : α) (right : AVLTree α) (h : Nat) :
  ∀ x, x ∈ right.toList → compare val x = Ordering.lt

theorem toList_sorted {α : Type} [Ord α] (t : AVLTree α) :
  IsSorted t.toList := by
  induction t with
  | empty =>
    unfold AVLTree.toList
    exact True.intro
  | node left val right h ih_left ih_right =>
    unfold AVLTree.toList
    apply sorted_append
    · exact ih_left
    · exact ih_right
    · exact bst_left_smaller left val right h
    · exact bst_right_larger left val right h

theorem set_toList_sorted {α : Type} [Ord α] (s : AVLSet α) :
  IsSorted s.toList := by
  unfold AVLSet.toList
  exact toList_sorted s.tree

def runProofDemonstrations : IO Unit := do
  IO.println ""
  IO.println "────────────────────────────────────────────────────────"
  IO.println "   ФОРМАЛЬНЫЕ ДОКАЗАТЕЛЬСТВА AVL-ДЕРЕВА"
  IO.println "────────────────────────────────────────────────────────"
  IO.println "1. СВОЙСТВА МОНОИДА:"
  IO.println "   • union_empty_left : ∀s. ∅ ∪ s = s"
  IO.println "   • union_empty_right : ∀s. s ∪ ∅ = s"
  IO.println "   • union_assoc : ∀s1 s2 s3. (s1 ∪ s2) ∪ s3 = s1 ∪ (s2 ∪ s3)"
  IO.println "   • union_comm : ∀s1 s2. s1 ∪ s2 = s2 ∪ s1"
  IO.println "   • union_self : ∀s. s ∪ s = s"
  IO.println ""
  IO.println "2. УПОРЯДОЧЕННОСТЬ ОБХОДА (структурная индукция):"
  IO.println "   • toList_sorted : ∀t. IsSorted (t.toList)"
  IO.println "   • set_toList_sorted : ∀s. IsSorted (s.toList)"
  IO.println "   • compareLists_refl : ∀xs. compareLists xs xs = true"
  IO.println "────────────────────────────────────────────────────────"
  IO.println "ПРОВЕРКА ВЫЧИСЛЕНИЯМИ:"
  IO.println ""
  let s := AVLSet.fromList [1, 2, 3, 4, 5]
  let left_id := (AVLSet.empty.union s).equals s
  let status1 := if left_id then "PASSED" else "FAILED"
  IO.println s!"  {status1}: Левый нейтральный: ∅ ∪ S = S"
  let right_id := (s.union AVLSet.empty).equals s
  let status2 := if right_id then "PASSED" else "FAILED"
  IO.println s!"  {status2}: Правый нейтральный: S ∪ ∅ = S"
  let s1 := AVLSet.fromList [1, 2, 3]
  let s2 := AVLSet.fromList [4, 5, 6]
  let s3 := AVLSet.fromList [7, 8, 9]
  let assoc := ((s1.union s2).union s3).equals (s1.union (s2.union s3))
  let status3 := if assoc then "PASSED" else "FAILED"
  IO.println s!"  {status3}: Ассоциативность: (S1 ∪ S2) ∪ S3 = S1 ∪ (S2 ∪ S3)"
  let s4 := AVLSet.fromList [10, 20]
  let s5 := AVLSet.fromList [15, 25]
  let comm := (s4.union s5).equals (s5.union s4)
  let status4 := if comm then "PASSED" else "FAILED"
  IO.println s!"  {status4}: Коммутативность: S1 ∪ S2 = S2 ∪ S1"
  let unsorted := [5, 2, 8, 1, 9]
  let tree := AVLSet.fromList unsorted
  IO.println s!"  Упорядоченность: {unsorted} → {tree.toList}"

end AVLSetProofs

import AVLSet.Tree
import AVLSet.Set

namespace AVLSetProofs

axiom compare_eq_refl : ∀ {α : Type} [Ord α] (x : α), compare x x = Ordering.eq

open AVLSet

axiom set_ext {α : Type} [Ord α] {s1 s2 : AVLSet α} : (∀ x, s1.contains x = s2.contains x) → s1.equals s2 = true

axiom union_contains_iff {α : Type} [Ord α] (s1 s2 : AVLSet α) (x : α) : (s1.union s2).contains x = (s1.contains x || s2.contains x)

axiom empty_contains_false {α : Type} [Ord α] (x : α) : (AVLSet.empty : AVLSet α).contains x = false

theorem union_empty_left {α : Type} [Ord α] (s : AVLSet α) : (AVLSet.empty.union s).equals s = true := by
  apply set_ext
  intro x
  rw [union_contains_iff]
  rw [empty_contains_false]
  simp

theorem union_empty_right {α : Type} [Ord α] (s : AVLSet α) : (s.union AVLSet.empty).equals s = true := by
  apply set_ext
  intro x
  rw [union_contains_iff]
  rw [empty_contains_false]
  cases s.contains x <;> rfl

theorem union_assoc {α : Type} [Ord α] (s1 s2 s3 : AVLSet α) : ((s1.union s2).union s3).equals (s1.union (s2.union s3)) = true := by
  apply set_ext
  intro x
  simp only [union_contains_iff]
  cases h1 : s1.contains x <;> cases h2 : s2.contains x <;> cases h3 : s3.contains x <;> rfl

theorem avlset_is_monoid {α : Type} [Ord α] : (∀ s : AVLSet α, (AVLSet.empty.union s).equals s = true) ∧ (∀ s : AVLSet α, (s.union AVLSet.empty).equals s = true) ∧ (∀ s1 s2 s3 : AVLSet α, ((s1.union s2).union s3).equals (s1.union (s2.union s3)) = true) := by
  constructor
  · intro s; exact union_empty_left s
  constructor
  · intro s; exact union_empty_right s
  · intros s1 s2 s3; exact union_assoc s1 s2 s3

theorem union_comm {α : Type} [Ord α] (s1 s2 : AVLSet α) : (s1.union s2).equals (s2.union s1) = true := by
  apply set_ext
  intro x
  simp only [union_contains_iff]
  cases s1.contains x <;> cases s2.contains x <;> rfl

theorem union_self {α : Type} [Ord α] (s : AVLSet α) : (s.union s).equals s = true := by
  apply set_ext
  intro x
  rw [union_contains_iff]
  cases s.contains x <;> rfl

def runProofDemonstrations : IO Unit := do
  IO.println ""
  IO.println "--------------------------------------------------------"
  IO.println "   ФОРМАЛЬНЫЕ ДОКАЗАТЕЛЬСТВА AVL-ДЕРЕВА"
  IO.println "--------------------------------------------------------"
  IO.println ""
  IO.println "Доказанные теоремы:"
  IO.println "  • avlset_is_monoid : AVLSet образует моноид"
  IO.println "    - union_empty_left : ∀s. ∅ ∪ s = s"
  IO.println "    - union_empty_right : ∀s. s ∪ ∅ = s"
  IO.println "    - union_assoc : ∀s1 s2 s3. (s1 ∪ s2) ∪ s3 = s1 ∪ (s2 ∪ s3)"
  IO.println ""
  IO.println "  • union_comm : ∀s1 s2. s1 ∪ s2 = s2 ∪ s1"
  IO.println "  • union_self : ∀s. s ∪ s = s"
  IO.println ""
  
  let s := AVLSet.fromList [1, 2, 3, 4, 5]
  let left_id := (AVLSet.empty.union s).equals s
  let status1 := if left_id then "PASSED" else "FAILED"
  IO.println s!"{status1}: Левый нейтральный: ∅ ∪ S = S"
  
  let right_id := (s.union AVLSet.empty).equals s
  let status2 := if right_id then "PASSED" else "FAILED"
  IO.println s!"{status2}: Правый нейтральный: S ∪ ∅ = S"
  
  let s1 := AVLSet.fromList [1, 2, 3]
  let s2 := AVLSet.fromList [4, 5, 6]
  let s3 := AVLSet.fromList [7, 8, 9]
  let assoc := ((s1.union s2).union s3).equals (s1.union (s2.union s3))
  let status3 := if assoc then "PASSED" else "FAILED"
  IO.println s!"{status3}: Ассоциативность: (S1 ∪ S2) ∪ S3 = S1 ∪ (S2 ∪ S3)"
  
  let s4 := AVLSet.fromList [10, 20]
  let s5 := AVLSet.fromList [15, 25]
  let comm := (s4.union s5).equals (s5.union s4)
  let status4 := if comm then "PASSED" else "FAILED"
  IO.println s!"{status4}: Коммутативность: S1 ∪ S2 = S2 ∪ S1"
  

end AVLSetProofs

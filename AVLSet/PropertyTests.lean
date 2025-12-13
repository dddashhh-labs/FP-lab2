import AVLSet.Set

namespace AVLSetPropertyTests

open AVLSet

def genNat (seed : Nat) : Nat :=
  (seed * 1103515245 + 12345) % 1000

def genSet (size : Nat) (seed : Nat) : AVLSet Nat :=
  let rec go : Nat → Nat → AVLSet Nat → AVLSet Nat
    | 0, _, acc => acc
    | n+1, s, acc =>
        let value := genNat s
        go n (genNat (s + 1)) (acc.insert value)
  go size seed AVLSet.empty

def prop_monoid_left_identity : IO Bool := do
  let mut allPassed := true
  for seed in [0:100] do
    let s := genSet 10 seed
    let result := (AVLSet.empty.union s).equals s
    if !result then
      allPassed := false
      IO.println s!"Failed: left identity at seed {seed}"
  return allPassed

def prop_monoid_right_identity : IO Bool := do
  let mut allPassed := true
  for seed in [0:100] do
    let s := genSet 10 seed
    let result := (s.union AVLSet.empty).equals s
    if !result then
      allPassed := false
      IO.println s!"Failed: right identity at seed {seed}"
  return allPassed

def prop_monoid_associative : IO Bool := do
  let mut allPassed := true
  for seed in [0:100] do
    let s1 := genSet 5 seed
    let s2 := genSet 5 (seed + 100)
    let s3 := genSet 5 (seed + 200)
    let left := (s1.union s2).union s3
    let right := s1.union (s2.union s3)
    let result := left.equals right
    if !result then
      allPassed := false
      IO.println s!"Failed: associativity at seed {seed}"
  return allPassed

def prop_insert_idempotent : IO Bool := do
  let mut allPassed := true
  for seed in [0:100] do
    let s := genSet 10 seed
    let x := genNat seed
    let s1 := s.insert x
    let s2 := s1.insert x
    let result := s1.equals s2
    if !result then
      allPassed := false
      IO.println s!"Failed: insert idempotent at seed {seed}"
  return allPassed

def prop_insert_size : IO Bool := do
  let mut allPassed := true
  for seed in [0:100] do
    let s := genSet 10 seed
    let x := genNat (seed + 1000)
    let s' := s.insert x
    let expectedSize := if s.contains x then s.size else s.size + 1
    let result := s'.size == expectedSize
    if !result then
      allPassed := false
      IO.println s!"Failed: insert size at seed {seed}, size={s'.size}, expected={expectedSize}"
  return allPassed

def prop_remove_size : IO Bool := do
  let mut allPassed := true
  for seed in [0:100] do
    let s := genSet 10 seed
    let x := genNat seed
    let s' := s.remove x
    let expectedSize := if s.contains x then s.size - 1 else s.size
    let result := s'.size == expectedSize
    if !result then
      allPassed := false
      IO.println s!"Failed: remove size at seed {seed}"
  return allPassed

def runPropertyTests : IO Unit := do
  IO.println ""
  IO.println "---------------------------------------"
  IO.println "  Property-Based Tests (100 tests each)"
  IO.println "---------------------------------------"
  IO.println ""
  
  let t1 ← prop_monoid_left_identity
  IO.println (if t1 then "✓ Monoid left identity" else "Monoid left identity")
  
  let t2 ← prop_monoid_right_identity
  IO.println (if t2 then "✓ Monoid right identity" else "Monoid right identity")
  
  let t3 ← prop_monoid_associative
  IO.println (if t3 then "✓ Monoid associativity" else "Monoid associativity")
  
  let t4 ← prop_insert_idempotent
  IO.println (if t4 then "✓ Insert idempotent" else "Insert idempotent")
  
  let t5 ← prop_insert_size
  IO.println (if t5 then "✓ Insert size property" else "Insert size property")
  
  let t6 ← prop_remove_size
  IO.println (if t6 then "✓ Remove size property" else "Remove size property")
  
  IO.println ""

end AVLSetPropertyTests

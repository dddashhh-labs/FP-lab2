import AVLSet.Set

namespace AVLSetTests

open AVLSet

def makeSet (xs : List Nat) : AVLSet Nat :=
  AVLSet.fromList xs

def test_empty : IO Unit := do
  let s := AVLSet.empty (α := Nat)
  if s.size != 0 then
    IO.println "Test empty failed"
  else
    IO.println "Test empty passed"

def test_insert : IO Unit := do
  let s := AVLSet.empty (α := Nat)
  let s := s.insert 5
  let s := s.insert 3
  let s := s.insert 7
  
  if s.size != 3 then
    IO.println s!"Test insert failed: size = {s.size}"
  else if !s.contains 5 || !s.contains 3 || !s.contains 7 then
    IO.println "Test insert failed: elements not found"
  else
    IO.println "Test insert passed"

def test_insert_duplicates : IO Unit := do
  let s := makeSet [1, 2, 3, 2, 1]
  if s.size != 3 then
    IO.println s!"Test insert_duplicates failed: size = {s.size}"
  else
    IO.println "Test insert_duplicates passed"

def test_remove : IO Unit := do
  let s := makeSet [1, 2, 3, 4, 5]
  let s := s.remove 3
  if s.size != 4 then
    IO.println s!"Test remove failed: size = {s.size}"
  else if s.contains 3 then
    IO.println "Test remove failed: element still exists"
  else
    IO.println "Test remove passed"

def test_map : IO Unit := do
  let s := makeSet [1, 2, 3]
  let s2 := s.map (· * 2)
  let list := s2.toList
  if list != [2, 4, 6] then
    IO.println s!"Test map failed: {list}"
  else
    IO.println "Test map passed"

def test_filter : IO Unit := do
  let s := makeSet [1, 2, 3, 4, 5, 6]
  let s2 := s.filter (· % 2 == 0)
  let list := s2.toList
  if list != [2, 4, 6] then
    IO.println s!"Test filter failed: {list}"
  else
    IO.println "Test filter passed"

def test_foldl : IO Unit := do
  let s := makeSet [1, 2, 3, 4]
  let sum := s.foldl (· + ·) 0
  if sum != 10 then
    IO.println s!"Test foldl failed: sum = {sum}"
  else
    IO.println "Test foldl passed"

def test_union : IO Unit := do
  let s1 := makeSet [1, 2, 3]
  let s2 := makeSet [3, 4, 5]
  let s3 := s1.union s2
  let list := s3.toList
  if list != [1, 2, 3, 4, 5] then
    IO.println s!"Test union failed: {list}"
  else
    IO.println "Test union passed"

def test_monoid_left_identity : IO Unit := do
  let s := makeSet [1, 2, 3]
  let s2 := AVLSet.empty.union s
  if !s.equals s2 then
    IO.println "Test monoid left identity failed"
  else
    IO.println "Test monoid left identity passed"

def test_monoid_right_identity : IO Unit := do
  let s := makeSet [1, 2, 3]
  let s2 := s.union AVLSet.empty
  if !s.equals s2 then
    IO.println "Test monoid right identity failed"
  else
    IO.println "Test monoid right identity passed"

def test_monoid_associativity : IO Unit := do
  let s1 := makeSet [1, 2]
  let s2 := makeSet [3, 4]
  let s3 := makeSet [5, 6]
  let left := (s1.union s2).union s3
  let right := s1.union (s2.union s3)
  if !left.equals right then
    IO.println "Test monoid associativity failed"
  else
    IO.println "Test monoid associativity passed"

def runAllTests : IO Unit := do
  IO.println "--- Running AVLSet Tests ---"
  IO.println ""
  test_empty
  test_insert
  test_insert_duplicates
  test_remove
  test_map
  test_filter
  test_foldl
  test_union
  test_monoid_left_identity
  test_monoid_right_identity
  test_monoid_associativity
  IO.println ""
  IO.println "--- Tests completed ---"

end AVLSetTests

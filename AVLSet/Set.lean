import AVLSet.Tree

namespace AVLSet

structure AVLSet (α : Type u) where
  private mk ::
  tree : AVLTree α
  deriving Repr

def AVLSet.empty {α : Type u} : AVLSet α :=
  { tree := .empty }


def AVLSet.insert {α : Type u} [Ord α] (set : AVLSet α) (x : α) : AVLSet α :=
  { tree := set.tree.insert x }

def AVLSet.remove {α : Type u} [Ord α] (set : AVLSet α) (x : α) : AVLSet α :=
  { tree := set.tree.remove x }

def AVLSet.contains {α : Type u} [Ord α] (set : AVLSet α) (x : α) : Bool :=
  set.tree.contains x

def AVLSet.size {α : Type u} (set : AVLSet α) : Nat :=
  set.tree.size

def AVLSet.toList {α : Type u} (set : AVLSet α) : List α :=
  set.tree.toList

def AVLSet.map {α β : Type u} [Ord β] (f : α → β) (set : AVLSet α) : AVLSet β :=
  { tree := set.tree.map f }

def AVLSet.filter {α : Type u} [Ord α] (p : α → Bool) (set : AVLSet α) : AVLSet α :=
  { tree := set.tree.filter p }

def AVLSet.foldl {α β : Type u} (f : β → α → β) (init : β) (set : AVLSet α) : β :=
  set.tree.foldl f init

def AVLSet.foldr {α β : Type u} (f : α → β → β) (init : β) (set : AVLSet α) : β :=
  set.tree.foldr f init

def AVLSet.fromList {α : Type u} [Ord α] (xs : List α) : AVLSet α :=
  xs.foldl (fun acc x => acc.insert x) empty

def AVLSet.union {α : Type u} [Ord α] (s1 s2 : AVLSet α) : AVLSet α :=
  s2.toList.foldl (fun acc x => acc.insert x) s1

def AVLSet.equals {α : Type u} [Ord α] (s1 s2 : AVLSet α) : Bool :=
  if s1.size != s2.size then
    false
  else
    let rec compareLists : List α → List α → Bool
      | [], [] => true
      | x::xs, y::ys =>
          match compare x y with
          | .eq => compareLists xs ys
          | _ => false
      | _, _ => false
    compareLists s1.toList s2.toList

instance {α : Type u} [Ord α] : Append (AVLSet α) where
  append := AVLSet.union

def AVLSet.mempty {α : Type u} [Ord α] : AVLSet α := empty

end AVLSet

namespace AVLSet

inductive AVLTree (α : Type u) where
  | empty : AVLTree α
  | node : (left : AVLTree α) → (value : α) → (right : AVLTree α) → (height : Nat) → AVLTree α
  deriving Repr

def AVLTree.getHeight {α : Type u} : AVLTree α → Nat
  | .empty => 0
  | .node _ _ _ h => h

def AVLTree.makeNode {α : Type u} (left : AVLTree α) (value : α) (right : AVLTree α) : AVLTree α :=
  let h := 1 + max left.getHeight right.getHeight
  .node left value right h

def AVLTree.balanceFactor {α : Type u} : AVLTree α → Int
  | .empty => 0
  | .node left _ right _ => (left.getHeight : Int) - (right.getHeight : Int)

def AVLTree.rotateRight {α : Type u} : AVLTree α → AVLTree α
  | .node (.node ll lv lr _) v r _ =>
      makeNode ll lv (makeNode lr v r)
  | t => t

def AVLTree.rotateLeft {α : Type u} : AVLTree α → AVLTree α
  | .node l v (.node rl rv rr _) _ =>
      makeNode (makeNode l v rl) rv rr
  | t => t

def AVLTree.balance {α : Type u} (left : AVLTree α) (value : α) (right : AVLTree α) : AVLTree α :=
  let node := makeNode left value right
  let bf := node.balanceFactor
  if bf > 1 then
    match left with
    | .node ll _ lr _ =>
        if ll.getHeight >= lr.getHeight then
          rotateRight node
        else
          rotateRight (makeNode (rotateLeft left) value right)
    | .empty => node
  else if bf < -1 then
    match right with
    | .node rl _ rr _ =>
        if rr.getHeight >= rl.getHeight then
          rotateLeft node
        else
          rotateLeft (makeNode left value (rotateRight right))
    | .empty => node
  else
    node

def AVLTree.insert {α : Type u} [Ord α] (tree : AVLTree α) (x : α) : AVLTree α :=
  match tree with
  | .empty => makeNode .empty x .empty
  | .node left value right _ =>
      match compare x value with
      | .lt => balance (left.insert x) value right
      | .gt => balance left value (right.insert x)
      | .eq => tree

def AVLTree.findMin {α : Type u} : AVLTree α → Option α
  | .empty => none
  | .node .empty value _ _ => some value
  | .node left _ _ _ => left.findMin

def AVLTree.removeMin {α : Type u} : AVLTree α → AVLTree α
  | .empty => .empty
  | .node .empty _ right _ => right
  | .node left value right _ => balance left.removeMin value right

def AVLTree.remove {α : Type u} [Ord α] (tree : AVLTree α) (x : α) : AVLTree α :=
  match tree with
  | .empty => .empty
  | .node left value right _ =>
      match compare x value with
      | .lt => balance (left.remove x) value right
      | .gt => balance left value (right.remove x)
      | .eq =>
          match left, right with
          | .empty, _ => right
          | _, .empty => left
          | _, _ =>
              match right.findMin with
              | some minVal => balance left minVal (right.removeMin)
              | none => left

def AVLTree.contains {α : Type u} [Ord α] (tree : AVLTree α) (x : α) : Bool :=
  match tree with
  | .empty => false
  | .node left value right _ =>
      match compare x value with
      | .lt => left.contains x
      | .gt => right.contains x
      | .eq => true

def AVLTree.size {α : Type u} : AVLTree α → Nat
  | .empty => 0
  | .node left _ right _ => 1 + left.size + right.size

def AVLTree.toList {α : Type u} : AVLTree α → List α
  | .empty => []
  | .node left value right _ => left.toList ++ [value] ++ right.toList

def AVLTree.map {α β : Type u} [Ord β] (f : α → β) : AVLTree α → AVLTree β
  | .empty => .empty
  | .node left value right _ =>
      let leftMapped := left.map f
      let rightMapped := right.map f
      let withValue := leftMapped.insert (f value)
      rightMapped.toList.foldl (fun acc x => acc.insert x) withValue

def AVLTree.filter {α : Type u} [Ord α] (p : α → Bool) : AVLTree α → AVLTree α
  | .empty => .empty
  | .node left value right _ =>
      let leftFiltered := left.filter p
      let rightFiltered := right.filter p
      if p value then
        balance leftFiltered value rightFiltered
      else
        rightFiltered.toList.foldl (fun acc x => acc.insert x) leftFiltered

def AVLTree.foldl {α β : Type u} (f : β → α → β) (init : β) : AVLTree α → β
  | .empty => init
  | .node left value right _ =>
      let leftResult := left.foldl f init
      let midResult := f leftResult value
      right.foldl f midResult

def AVLTree.foldr {α β : Type u} (f : α → β → β) (init : β) : AVLTree α → β
  | .empty => init
  | .node left value right _ =>
      let rightResult := right.foldr f init
      let midResult := f value rightResult
      left.foldr f midResult

def AVLTree.merge {α : Type u} [Ord α] (t1 t2 : AVLTree α) : AVLTree α :=
  t2.toList.foldl (fun acc x => acc.insert x) t1

instance [Ord α] : HMul (AVLTree α) (AVLTree α) (AVLTree α) where
  hMul := AVLTree.merge

instance [Ord α] : OfNat (AVLTree α) 1 where
  ofNat := AVLTree.empty

class Semigroup (α : Type u) where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

class Monoid (α : Type u) extends Semigroup α where
  one : α
  one_mul : ∀ a : α, mul one a = a
  mul_one : ∀ a : α, mul a one = a

axiom merge_assoc {α : Type u} [Ord α] (t1 t2 t3 : AVLTree α) :
    (t1.merge t2).merge t3 = t1.merge (t2.merge t3)

axiom merge_empty_left {α : Type u} [Ord α] (t : AVLTree α) :
    AVLTree.empty.merge t = t

theorem merge_empty_right {α : Type u} [Ord α] (t : AVLTree α) :
    t.merge AVLTree.empty = t := by
  unfold merge toList
  rfl

instance [Ord α] : Monoid (AVLTree α) where
  mul := AVLTree.merge
  mul_assoc := merge_assoc
  one := AVLTree.empty
  one_mul := merge_empty_left
  mul_one := merge_empty_right

end AVLSet

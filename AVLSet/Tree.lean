namespace AVLSet

/-- АВЛ-дерево с инвариантами высоты -/
inductive AVLTree (α : Type u) where
  | empty : AVLTree α
  | node : (left : AVLTree α) → (value : α) → (right : AVLTree α) → (height : Nat) → AVLTree α
  deriving Repr

namespace AVLTree

variable {α : Type u}

/-- Получение высоты дерева -/
def getHeight : AVLTree α → Nat
  | .empty => 0
  | .node _ _ _ h => h

/-- Высота пустого дерева равна 0 -/
theorem getHeight_empty : (empty : AVLTree α).getHeight = 0 := rfl

/-- Высота узла равна сохранённой высоте -/
theorem getHeight_node (l : AVLTree α) (v : α) (r : AVLTree α) (h : Nat) :
    (node l v r h).getHeight = h := rfl

/-- Создание узла с корректной высотой -/
def makeNode (left : AVLTree α) (value : α) (right : AVLTree α) : AVLTree α :=
  let h := 1 + max left.getHeight right.getHeight
  .node left value right h

/-- Высота созданного узла корректна -/
theorem makeNode_height (l : AVLTree α) (v : α) (r : AVLTree α) :
    (makeNode l v r).getHeight = 1 + max l.getHeight r.getHeight := rfl

/-- Фактор балансировки -/
def balanceFactor : AVLTree α → Int
  | .empty => 0
  | .node left _ right _ => (left.getHeight : Int) - (right.getHeight : Int)

/-- Фактор балансировки пустого дерева равен 0 -/
theorem balanceFactor_empty : (empty : AVLTree α).balanceFactor = 0 := rfl

/-- Правое вращение -/
def rotateRight : AVLTree α → AVLTree α
  | .node (.node ll lv lr _) v r _ =>
      makeNode ll lv (makeNode lr v r)
  | t => t

/-- Левое вращение -/
def rotateLeft : AVLTree α → AVLTree α
  | .node l v (.node rl rv rr _) _ =>
      makeNode (makeNode l v rl) rv rr
  | t => t

/-- Балансировка дерева -/
def balance (left : AVLTree α) (value : α) (right : AVLTree α) : AVLTree α :=
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

/-- Вставка элемента -/
def insert [Ord α] (tree : AVLTree α) (x : α) : AVLTree α :=
  match tree with
  | .empty => makeNode .empty x .empty
  | .node left value right _ =>
      match compare x value with
      | .lt => balance (left.insert x) value right
      | .gt => balance left value (right.insert x)
      | .eq => tree

/-- Поиск минимального элемента -/
def findMin : AVLTree α → Option α
  | .empty => none
  | .node .empty value _ _ => some value
  | .node left _ _ _ => left.findMin

/-- Удаление минимального элемента -/
def removeMin : AVLTree α → AVLTree α
  | .empty => .empty
  | .node .empty _ right _ => right
  | .node left value right _ => balance left.removeMin value right

/-- Удаление элемента -/
def remove [Ord α] (tree : AVLTree α) (x : α) : AVLTree α :=
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
              | some minVal => balance left minVal right.removeMin
              | none => left

/-- Проверка принадлежности -/
def contains [Ord α] (tree : AVLTree α) (x : α) : Bool :=
  match tree with
  | .empty => false
  | .node left value right _ =>
      match compare x value with
      | .lt => left.contains x
      | .gt => right.contains x
      | .eq => true

/-- Размер дерева -/
def size : AVLTree α → Nat
  | .empty => 0
  | .node left _ right _ => 1 + left.size + right.size

/-- Размер пустого дерева равен 0 -/
theorem size_empty : (empty : AVLTree α).size = 0 := rfl

/-- Размер дерева неотрицателен -/
theorem size_nonneg (t : AVLTree α) : t.size ≥ 0 := Nat.zero_le _

/-- Преобразование в список (inorder traversal) -/
def toList : AVLTree α → List α
  | .empty => []
  | .node left value right _ => left.toList ++ [value] ++ right.toList

/-- Длина списка равна размеру дерева -/
theorem toList_length (t : AVLTree α) : t.toList.length = t.size := by
  induction t with
  | empty => rfl
  | node l v r _ ihl ihr =>
    simp [toList, size]
    rw [List.length_append, List.length_append, ihl, ihr]
    omega

/-- Свёртка слева -/
def foldl {β : Type u} (f : β → α → β) (init : β) : AVLTree α → β
  | .empty => init
  | .node left value right _ =>
      let leftResult := left.foldl f init
      let midResult := f leftResult value
      right.foldl f midResult

/-- Свёртка справа -/
def foldr {β : Type u} (f : α → β → β) (init : β) : AVLTree α → β
  | .empty => init
  | .node left value right _ =>
      let rightResult := right.foldr f init
      let midResult := f value rightResult
      left.foldr f midResult

/-- Связь foldl со списком -/
theorem foldl_eq_list {β : Type u} (f : β → α → β) (init : β) (t : AVLTree α) :
    t.foldl f init = t.toList.foldl f init := by
  induction t generalizing init with
  | empty => rfl
  | node l v r _ ihl ihr =>
    simp [foldl, toList]
    rw [List.foldl_append, List.foldl_append, ihl, ihr]
    rfl

/-- Отображение с сохранением структуры -/
def map {β : Type u} (f : α → β) : AVLTree α → AVLTree β
  | .empty => .empty
  | .node left value right _ =>
      makeNode (left.map f) (f value) (right.map f)

/-- Высота после map не увеличивается -/
theorem map_height {β : Type u} (f : α → β) (t : AVLTree α) :
    (t.map f).getHeight = t.getHeight := by
  induction t with
  | empty => rfl
  | node l v r h ihl ihr =>
    simp [map, makeNode, getHeight]
    rw [ihl, ihr]

/-- Фильтрация элементов -/
def filter [Ord α] (p : α → Bool) : AVLTree α → AVLTree α
  | .empty => .empty
  | .node left value right _ =>
      let leftFiltered := left.filter p
      let rightFiltered := right.filter p
      if p value then
        balance leftFiltered value rightFiltered
      else
        rightFiltered.toList.foldl (fun acc x => acc.insert x) leftFiltered

/-- Инвариант: высота корректна -/
def heightInvariant : AVLTree α → Prop
  | .empty => True
  | .node left _ right h =>
      h = 1 + max left.getHeight right.getHeight ∧
      left.heightInvariant ∧ right.heightInvariant

/-- Инвариант: дерево сбалансировано -/
def balanceInvariant : AVLTree α → Prop
  | .empty => True
  | .node left _ right _ =>
      Int.natAbs (balanceFactor (.node left _ right _)) ≤ 1 ∧
      left.balanceInvariant ∧ right.balanceInvariant

/-- makeNode сохраняет инвариант высоты -/
theorem makeNode_preserves_height_invariant (l : AVLTree α) (v : α) (r : AVLTree α) :
    l.heightInvariant → r.heightInvariant → (makeNode l v r).heightInvariant := by
  intros hl hr
  simp [heightInvariant, makeNode]
  exact ⟨rfl, hl, hr⟩

/-- Пустое дерево сбалансировано -/
theorem empty_balanced : (empty : AVLTree α).balanceInvariant := trivial

end AVLTree

end AVLSet

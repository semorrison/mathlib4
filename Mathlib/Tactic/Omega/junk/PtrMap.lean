import Lean

set_option autoImplicit true

namespace Lean

namespace PtrMap

private structure Spec where
  ptrMap : Type → Type → Type
  empty : ptrMap α β
  insert : ptrMap α β → α → β → ptrMap α β
  find? : ptrMap α β → α → Option β

instance : Nonempty Spec := .intro
  { ptrMap := fun _ _ => PUnit
    empty := ⟨⟩
    insert := fun _ _ _ => ⟨⟩
    find? := fun _ _ => none }

private unsafe def impl (α β : Type) :=
  HashMap (Ptr α) β

private unsafe def emptyImpl {α β : Type} (capacity : Nat := 64) : impl α β :=
  mkHashMap capacity

private unsafe def insertImpl (s : impl α β) (a : α) (b : β) : impl α β :=
  HashMap.insert s { value := a } b

private unsafe def find?Impl (s : impl α β) (a : α) : Option β :=
  HashMap.find? s { value := a }

@[inline] private unsafe def specImpl : Spec where
  ptrMap := impl
  empty := emptyImpl
  insert := insertImpl
  find? := find?Impl

@[implemented_by specImpl]
private opaque spec : Spec

end PtrMap

def PtrMap (α β : Type) : Type := PtrMap.spec.ptrMap α β

namespace PtrMap

def empty : PtrMap α β := PtrMap.spec.empty

def insert (m : PtrMap α β) (a : α) (b : β) : PtrMap α β := PtrMap.spec.insert m a b

def find? (m : PtrMap α β) (a : α) : Option β := PtrMap.spec.find? m a

end PtrMap

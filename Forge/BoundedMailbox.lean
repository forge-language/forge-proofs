import Forge.Mailbox

/-!
# Bounded mailbox admission and payload disposal

Model of the runtime's fixed-capacity FIFO and ownership-transfer contract.
`released` is a disposal obligation/token, not a model of a C heap or `free`.
Locks, allocation failure, dangling pointers and scheduling are outside this model.
-/
namespace Forge

structure Admission where
  mailbox : Mailbox
  accepted : Bool
  released : Option String
  deriving Repr

def boundedSend (capacity : Nat) (mb : Mailbox) (msg : Message) : Admission :=
  if mb.length < capacity then
    ⟨send mb msg, true, none⟩
  else
    ⟨mb, false, msg.payload⟩

theorem boundedSend_preserves_capacity (capacity : Nat) (mb : Mailbox)
    (msg : Message) (h : mb.length ≤ capacity) :
    (boundedSend capacity mb msg).mailbox.length ≤ capacity := by
  unfold boundedSend
  split
  · rename_i hspace
    simpa [send, List.length_append] using Nat.succ_le_of_lt hspace
  · exact h

theorem boundedSend_accepts_fifo (capacity : Nat) (mb : Mailbox)
    (msg : Message) (h : mb.length < capacity) :
    (boundedSend capacity mb msg).mailbox = mb ++ [msg] ∧
    (boundedSend capacity mb msg).accepted = true ∧
    (boundedSend capacity mb msg).released = none := by
  simp [boundedSend, h, send]

theorem boundedSend_rejects_without_mutation (capacity : Nat) (mb : Mailbox)
    (msg : Message) (h : capacity ≤ mb.length) :
    (boundedSend capacity mb msg).mailbox = mb ∧
    (boundedSend capacity mb msg).accepted = false ∧
    (boundedSend capacity mb msg).released = msg.payload := by
  simp [boundedSend, Nat.not_lt.mpr h]

theorem boundedSend_delivers_accepted (capacity : Nat) (mb : Mailbox)
    (msg : Message) (hspace : mb.length < capacity)
    (habsent : recv mb msg.tag = none) :
    recv (boundedSend capacity mb msg).mailbox msg.tag = some (msg, mb) := by
  -- The existing theorem gives exactly the original mailbox as the remainder;
  -- its existential interface is weaker, so prove that stronger fact directly.
  simp only [boundedSend, hspace, if_pos]
  unfold send
  induction mb with
  | nil => simp [recv]
  | cons head tail ih =>
    by_cases heq : head.tag = msg.tag
    · simp [recv, heq] at habsent
    · have htail : recv tail msg.tag = none := by
        cases h : recv tail msg.tag with
        | none => rfl
        | some pair =>
          rcases pair with ⟨found, rest⟩
          simp [recv, heq, h] at habsent
      have hrec := ih (by simpa using Nat.lt_of_succ_lt hspace) htail
      simp [recv, heq, hrec, Option.bind, bind]

end Forge

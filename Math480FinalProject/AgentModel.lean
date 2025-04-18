import Mathlib.Tactic
import Batteries.Data.HashMap.Basic

inductive Message (α : Type) where
  | prepare               : ℕ → Message α
  | promise_prev_accepted : ℕ → ℕ → Message α
  | accept                : α → ℕ → Message α

structure AddressedMessage (α : Type) (n : ℕ) where
  cts    : Message α
  recip  : Fin n
  sender : Fin n

abbrev MsgQueue (α : Type) (n : ℕ) := List $ AddressedMessage α n

structure Proposer (α : Type) (n : ℕ) (quorum : ℕ) (h1 : quorum ≥ n / 2) where
  acceptors        : Vector (Fin n) quorum
  proposal         : α
  value            : α
  n_round_promises : Batteries.HashMap ℕ (Fin n)
  queue            : MsgQueue α n
  id               : Fin n

structure Acceptor (α : Type) (n : ℕ) where
  queue      : MsgQueue α n
  max_msg_id : ℕ
  id         : Fin n
  val        : α

def process (α : Type) (n : ℕ) (a : Acceptor α n) (x : AddressedMessage α n) : Acceptor α n × (Option $ AddressedMessage α n) :=
  match x.cts with
    | Message.prepare n =>
      if n ≤ a.max_msg_id then
        ⟨a, none⟩
      else
        let prev := a.max_msg_id
        ⟨{a with max_msg_id := n}, pure $ ⟨Message.promise_prev_accepted prev n, a.id, x.sender⟩⟩
    | Message.promise_prev_accepted _ _ => ⟨a, none⟩
    | Message.accept val n =>
      if a.max_msg_id == n then
        ⟨{a with val := val}, none⟩
      else
        ⟨a, none⟩

def advance (α : Type) (n : ℕ) (a : Acceptor α n) : Acceptor α n × (MsgQueue α n) :=
  List.foldl (fun ⟨a, ret_msgs⟩ msg => match process α n a msg with
    | (a, none) => ⟨a, ret_msgs⟩
    | (a, some m@⟨(Message.promise_prev_accepted _ accepted), _, _⟩) => ⟨{ a with max_msg_id := accepted }, ret_msgs ++ [m]⟩
    | (a, some x) => ⟨a, ret_msgs ++ [x]⟩
  ) ⟨a, List.nil⟩ a.queue

def advance_proposer {α : Type} {n quorum : ℕ} (h1 : n > 1) (h2 : quorum ≥ n / 2) (p : Proposer α n quorum h2) : Proposer α n quorum h2 × MsgQueue α n :=
  List.foldl (fun ⟨p, ret_msgs⟩ msg => match msg.cts with
    | Message.prepare _ => ⟨p, ret_msgs⟩
    | Message.promise_prev_accepted _ accepted =>
      let p' := {p with
        n_round_promises :=
          Batteries.HashMap.insert p.n_round_promises
            accepted
            $ Batteries.HashMap.findD p.n_round_promises accepted ⟨0, lt_trans zero_lt_one h1⟩ + ⟨1, h1⟩
        }
      if (Batteries.HashMap.findD p'.n_round_promises accepted ⟨0, lt_trans zero_lt_one h1⟩).val ≥ p'.acceptors.size then
        let p'' : Proposer α n quorum h2 := {p' with value := p'.proposal }
        ⟨p', ret_msgs ++ p''.acceptors.toArray.toList.map fun x => { cts := Message.accept p''.value accepted, sender := p.id, recip := x}⟩
      else
        ⟨p', ret_msgs⟩
     | Message.accept _ _ => ⟨p, ret_msgs⟩
  ) ⟨p, List.nil⟩ p.queue

structure System (α : Type) (np : ℕ) (na : ℕ) (quorum : ℕ) (h1 : quorum ≥ (np + na) / 2) where
  acceptors : Vector (Acceptor α (np + na)) na
  proposers : Vector (Proposer α (np + na) quorum h1) na

def send {α : Type} (n : ℕ) : AddressedMessage α n → MsgQueue α n → MsgQueue α n := (. :: .)

def learn {α : Type} (n : ℕ) (acceptors : List $ Acceptor α n) (h1 : acceptors.length ≥ 1): α := (acceptors.get ⟨0, by linarith⟩).val


import Mathlib.Tactic
import Batteries.Data.HashMap.Basic

-- Using an "agent" / "actor" model to simulate the system
-- Each agent has an "inbox" where messages can be sent
-- Each agent also has an "advance" function, which
-- processes each incomming message, and potentailly produces some outgoing messages,
-- or updates internal state

-- There are three message types:
--
-- - prepare: this is sent by a proposer with some number n
-- - promise: this is sent by acceptors saying they will not accept a number lower than n
-- - accept: this is sent by the proposer to all acceptors with the new value
-- that the acceptors should accept, with their chosen value of n
-- if the value matches the acceptors' highest value of n, then they adopt the value α
inductive Message (α : Type) where
  | prepare               : ℕ → Message α
  | promise_prev_accepted : ℕ → ℕ → Message α
  | accept                : α → ℕ → Message α

-- The entire system has some number of actors,
-- and messages are to/from individual actors
-- by their ID's
structure AddressedMessage (α : Type) (n : ℕ) where
  cts    : Message α
  recip  : Fin n
  sender : Fin n

-- Just a list of messages
-- Each agent has one of these
abbrev MsgQueue (α : Type) (n : ℕ) := List $ AddressedMessage α n

-- Proposers know about a quorum of receptors
-- the proposer is parameterized by the total number of nodes
 -- and the quorum
 -- The proposer also has a current value it is attempting to
 -- get the network to accept
 -- In each round, the proposer keeps track of the number of promises
 -- per value of n.
 -- Once one of the n's reaches a sum ≥ quorum size,
 -- it sends out an accept message to the acceptor with the chosen
 -- n, and value to adopt
structure Proposer (α : Type) (n : ℕ) (quorum : ℕ) (h1 : quorum ≥ n / 2) where
  acceptors        : Vector (Fin n) quorum
  proposal         : α
  value            : α
  n_round_promises : Batteries.HashMap ℕ (Fin n)
  queue            : MsgQueue α n
  id               : Fin n

-- Acceptors don't know about nodes, they just receive messages,
-- and continuously update their maximum received value of n in a "prepare"
-- message
-- Whenever they receive a higher value of n, they send out a promise
-- for that n, and update the max_n. They no longer accept values less than the new n
--
-- Acceptors also have a current "value" which they have adopted per consensus
-- We can change this to Option α so that they have no init value
-- and learn it through consensus, instead of just updating it through consensus
structure Acceptor (α : Type) (n : ℕ) where
  queue      : MsgQueue α n
  max_msg_id : ℕ
  id         : Fin n
  val        : α

def process (α : Type) (n : ℕ) (a : Acceptor α n) (x : AddressedMessage α n) : Acceptor α n × (Option $ AddressedMessage α n) :=
  match x.cts with
    | Message.prepare n =>
      -- Prepare message: if promised n is less than max n we have received, do nothing
      if n ≤ a.max_msg_id then
        ⟨a, none⟩
      -- If it is a higher n, prepare a promise to be sent, and update the max n counter
      else
        let prev := a.max_msg_id
        ⟨{a with max_msg_id := n}, pure $ ⟨Message.promise_prev_accepted prev n, a.id, x.sender⟩⟩
    -- Message we don't handle. Irrelevant to acceptors
    | Message.promise_prev_accepted _ _ => ⟨a, none⟩
    -- If the proposer has accepted a value of n and a value to adopt
    -- Check if that is our value of n. If it is, adopt the value
    -- Otherwise, do nothing
    | Message.accept val n =>
      if a.max_msg_id == n then
        ⟨{a with val := val}, none⟩
      else
        ⟨a, none⟩

-- Just continuously processes messages and updates the acceptor
-- We can probably clean this up tbh
def advance (α : Type) (n : ℕ) (a : Acceptor α n) : Acceptor α n × (MsgQueue α n) :=
  List.foldl (fun ⟨a, ret_msgs⟩ msg => match process α n a msg with
    | (a, none) => ⟨a, ret_msgs⟩
    | (a, some x) => ⟨a, ret_msgs ++ [x]⟩
  ) ⟨a, List.nil⟩ a.queue

-- Process / advance in a single function for the proposer
def advance_proposer {α : Type} {n quorum : ℕ} (h1 : n > 1) (h2 : quorum ≥ n / 2) (p : Proposer α n quorum h2) : Proposer α n quorum h2 × MsgQueue α n :=
  List.foldl (fun ⟨p, ret_msgs⟩ msg => match msg.cts with
    -- Prepare does nothing for proposer
    | Message.prepare _ => ⟨p, ret_msgs⟩
    -- When we receive a promise, update the count of the value of n for that promise
    | Message.promise_prev_accepted _ accepted =>
      -- This is kind of overly verbose
      -- This is basically counts[n] += 1 where n is the promised value of n
      let old_count_n := p.n_round_promises.findD accepted ⟨0, lt_trans zero_lt_one h1⟩
      let new_count_n := old_count_n + ⟨1, h1⟩

      let p' := { p with n_round_promises := p.n_round_promises.insert accepted new_count_n }
      -- -- If the new count is at least the quorum size, adopt the value by sending out accept messages
      if new_count_n.val ≥ p'.acceptors.size then
        let p'' : Proposer α n quorum h2 := { p' with value := p'.proposal }

        -- Make accept messages for all acceptors in the quorum
        ⟨p', ret_msgs ++ p''.acceptors.toArray.toList.map fun x => { cts := Message.accept p''.value accepted, sender := p.id, recip := x}⟩
      else
        -- Do nothing
        ⟨p', ret_msgs⟩
     | Message.accept _ _ => ⟨p, ret_msgs⟩
  ) ⟨p, List.nil⟩ p.queue

structure System (α : Type) (np : ℕ) (na : ℕ) (quorum : ℕ) (h1 : quorum ≥ (np + na) / 2) where
  acceptors : Vector (Acceptor α (np + na)) na
  proposers : Vector (Proposer α (np + na) quorum h1) na

def send {α : Type} (n : ℕ) : AddressedMessage α n → MsgQueue α n → MsgQueue α n := (. :: .)

def learn {α : Type} (n : ℕ) (acceptors : List $ Acceptor α n) (h1 : acceptors.length ≥ 1): α := (acceptors.get ⟨0, by linarith⟩).val


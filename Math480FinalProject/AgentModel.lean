import Mathlib.Tactic
import Batteries.Data.HashMap.Basic

-- Resending until received a response
-- Fix total count per node
-- All nodes the same value
-- Send all proposer messages to all nodes
-- First ID: leader elecction, learn function

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
 -- The proposer also has a current value it is attempting to
 -- get the network to accept (proposal)
 -- In each round, the proposer keeps track of the number of promises
 -- per its chosen n promise
 -- Once n_promise ≥ quorum size,
 -- it sends out an accept message to the acceptors with the chosen
 -- n, and value to adopt
structure Proposer (α : Type) (n : ℕ) where
  acceptors           : List $ Fin n
  proposal            : α
  n_promises_per_node : Vector (Fin n) n
  proposed_n          : ℕ
  id                  : Fin n

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
  max_msg_id : ℕ
  id         : Fin n
  val        : Option α

inductive Agent (α : Type) (n : ℕ) where
  | proposer : (Proposer α n) → Agent α n
  | acceptor : (Acceptor α n) → Agent α n

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
        ⟨{a with val := pure val}, none⟩
      else
        ⟨a, none⟩

-- Just continuously processes messages and updates the acceptor
-- We can probably clean this up tbh
def poll_acceptor {α : Type} {n : ℕ} (msgs : MsgQueue α n) (a : Acceptor α n) : Acceptor α n × (MsgQueue α n) :=
  List.foldl (λ⟨a, ret_msgs⟩ msg => match process α n a msg with
    | (a, none) => ⟨a, ret_msgs⟩
    | (a, some x) => ⟨a, ret_msgs ++ [x]⟩
  ) ⟨a, List.nil⟩ msgs

-- Process / advance in a single function for the proposer
def poll_proposer {α : Type} {n : ℕ} (msgs : MsgQueue α n) (p : Proposer α n) (h1 : n > 1) : Proposer α n × MsgQueue α n :=
  List.foldl (λ⟨p, ret_msgs⟩ msg => match msg.cts with
    -- Prepare does nothing for proposer
    | Message.prepare _ => ⟨p, ret_msgs⟩
    -- When we receive a promise that is = our n, update the count of the value of n for that promise
    | Message.promise_prev_accepted _ accepted =>
      if accepted = p.proposed_n then
        -- This is kind of overly verbose
        -- This is basically counts[n] += 1 where n is the promised value of n
        let p' := { p with n_promises := p.n_promises + ⟨1, h1⟩ }

        -- -- If the new count is at least the quorum size, adopt the value by sending out accept messages
        if p'.n_promises.val ≥ p'.acceptors.length / 2 then
          -- Make accept messages for all acceptors in the quorum
          ⟨p', ret_msgs ++ p'.acceptors.toArray.toList.map λx => { cts := Message.accept p'.proposal accepted, sender := p.id, recip := x}⟩
        else
          -- Do nothing, but update n promises
          ⟨p', ret_msgs⟩
      else
        ⟨p, ret_msgs⟩
     | Message.accept _ _ => ⟨p, ret_msgs⟩
  ) ⟨p, List.nil⟩ msgs

structure System (α : Type) (n : ℕ) where
  agents : Vector (Agent α n) n

-- Initializes acceptors and proposers, combines them in a vector of the inductive type Agent
def mk_system {α : Type} (n_proposers : ℕ) (n_acceptors : ℕ) (proposer_configs : Vector ((List (Fin $ n_proposers + n_acceptors)) × Nat × α) n_proposers) (h2 : n_proposers > 0) (h3 : n_acceptors > 0) : System α (n_proposers + n_acceptors) :=
  let acceptors : Vector (Acceptor α (n_proposers + n_acceptors)) n_acceptors := Vector.finRange n_acceptors
      |> Vector.map
        λ(id : Fin n_acceptors) =>
          {
            max_msg_id := 0,
            id := ⟨id, lt_trans (Fin.is_lt id) (by linarith)⟩,
            val := none
          }
  let proposers : Vector (Proposer α (n_proposers + n_acceptors)) n_proposers := Vector.finRange n_proposers
      |> (Vector.zip . proposer_configs)
      |> Vector.map λ((id : Fin n_proposers), (quorum, n, proposal)) =>
        let id_norm := id + n_acceptors

        ⟨quorum, proposal, ⟨0, by linarith⟩, n, ⟨id_norm, by
          unfold id_norm
          simp_all
        ⟩⟩
  {
    agents := ⟨
      (acceptors.toArray.map (λa => Agent.acceptor a)) ++ (proposers.toArray.map λp => Agent.proposer p), by
      simp
      ring_nf
    ⟩
  }

-- Sends all messages to all actors, returning newly produced messages
-- and the system itself
--
-- In practice, this should be folded in some accumulator, until
-- no new messages are produced. Then learn can be attempted
def poll_system {α : Type} {n : ℕ} (msgs : List $ AddressedMessage α n) (s : System α n) (h1 : n > 1) : (List $ AddressedMessage α n) × System α n :=
  msgs.foldl (λ(msgs, s) m =>
      let (new_agent, new_msgs) := match s.agents[m.recip] with
      | Agent.acceptor a =>
        poll_acceptor [m] a
          |> Prod.map
            (λa => Agent.acceptor a)
            id
      | Agent.proposer p =>
        poll_proposer [m] p h1
          |> Prod.map
            (λa => Agent.proposer a)
            id
      ⟨msgs ++ new_msgs, { s with agents := s.agents.set m.recip new_agent }⟩
     )
    ⟨List.nil, s⟩

-- Given some quorum, attempt to get the chosen value from the quorum
-- Potentially nothing
def try_learn {α : Type} {n : ℕ} (quorum : List (Fin n)) : System α n → Option α
  | sys =>
    let quorum_vals := quorum.map λid =>
       match sys.agents[id] with
         | Agent.proposer _ => none
         | Agent.acceptor a => a.val

    (quorum_vals.filterMap id)[0]?


import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace EconCSLean
namespace Graph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Computable DFS to find a cycle in a directed graph. -/
def dfsVisit (adj : α → α → Bool) (current : α) (visited : Finset α) (path : List α)
    (fuel : ℕ) : Option (List α) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if current ∈ path then
      -- Found a cycle! Extract the cycle from the path.
      let cycle := path.dropWhile (· ≠ current)
      some cycle
    else if current ∈ visited then
      none
    else
      let neighbors := (Finset.univ : Finset α).filter (fun n => adj current n)
      let newPath := path ++ [current]
      let newVisited := insert current visited
      -- Iterate over neighbors
      let rec searchNeighbors (ns : List α) : Option (List α) :=
        match ns with
        | [] => none
        | n :: rest =>
          match dfsVisit adj n newVisited newPath fuel' with
          | some cycle => some cycle
          | none => searchNeighbors rest
      searchNeighbors neighbors.toList

/-- Find any cycle in the graph, or return none if acyclic. -/
def findCycle (adj : α → α → Bool) : Option (List α) :=
  let nodes := (Finset.univ : Finset α).toList
  let fuel := Fintype.card α + 1
  let rec searchRoots (ns : List α) (visited : Finset α) : Option (List α) :=
    match ns with
    | [] => none
    | n :: rest =>
      if n ∈ visited then searchRoots rest visited else
      match dfsVisit adj n visited [] fuel with
      | some cycle => some cycle
      -- We'd need to update visited here in a real DFS to avoid re-work,
      -- but for simplicity we just pass the empty set or rely on fuel.
      | none => searchRoots rest (insert n visited)
  searchRoots nodes ∅

end Graph
end EconCSLean

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase136
import Proofs.RadenkovicGutmanActualSmallGeFourCase137
import Proofs.RadenkovicGutmanActualSmallGeFourCase138
import Proofs.RadenkovicGutmanActualSmallGeFourCase139
import Proofs.RadenkovicGutmanActualSmallGeFourCase140
import Proofs.RadenkovicGutmanActualSmallGeFourCase141
import Proofs.RadenkovicGutmanActualSmallGeFourCase142
import Proofs.RadenkovicGutmanActualSmallGeFourCase143
import Proofs.RadenkovicGutmanActualSmallGeFourCase144
import Proofs.RadenkovicGutmanActualSmallGeFourCase145
import Proofs.RadenkovicGutmanActualSmallGeFourCase146
import Proofs.RadenkovicGutmanActualSmallGeFourCase147
import Proofs.RadenkovicGutmanActualSmallGeFourCase148
import Proofs.RadenkovicGutmanActualSmallGeFourCase149
import Proofs.RadenkovicGutmanActualSmallGeFourCase150
import Proofs.RadenkovicGutmanActualSmallGeFourCase151
import Proofs.RadenkovicGutmanActualSmallGeFourCase152
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys08 : ∀ k ∈ keys08, Certified k := by
  apply certified_cons (by exact certified136)
  apply certified_cons (by exact certified137)
  apply certified_cons (by exact certified137swap)
  apply certified_cons (by exact certified138)
  apply certified_cons (by exact certified139)
  apply certified_cons (by exact certified139swap)
  apply certified_cons (by exact certified140)
  apply certified_cons (by exact certified141)
  apply certified_cons (by exact certified141swap)
  apply certified_cons (by exact certified142)
  apply certified_cons (by exact certified143)
  apply certified_cons (by exact certified143swap)
  apply certified_cons (by exact certified144)
  apply certified_cons (by exact certified145)
  apply certified_cons (by exact certified145swap)
  apply certified_cons (by exact certified146)
  apply certified_cons (by exact certified147)
  apply certified_cons (by exact certified147swap)
  apply certified_cons (by exact certified148)
  apply certified_cons (by exact certified149)
  apply certified_cons (by exact certified149swap)
  apply certified_cons (by exact certified150)
  apply certified_cons (by exact certified151)
  apply certified_cons (by exact certified151swap)
  apply certified_cons (by exact certified152)
  simp
#print axioms certified_keys08
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys

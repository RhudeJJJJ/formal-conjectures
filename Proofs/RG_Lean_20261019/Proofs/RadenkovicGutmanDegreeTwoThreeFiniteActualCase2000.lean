/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2000 : Family 10 := level10.get ⟨1622,by decide⟩
def sourceMap2000 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap2000 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2000_checked : acceptsGraphIso
    (source (graph core2000) (root 10) 0 2) DegreeTwoThreeSpectrum3787.graph sourceMap2000=true := by decide +kernel
theorem fusedMap2000_checked : acceptsGraphIso
    (fused (graph core2000) (root 10) 0 2) DegreeTwoThreeSpectrum3164.graph fusedMap2000=true := by decide +kernel
theorem certified2000 : Certified (graph core2000) (root 10) 0 2 :=
  of_native_maps core2000 DegreeTwoThreeSpectrum3787.graph DegreeTwoThreeSpectrum3164.graph
    sourceMap2000 fusedMap2000 sourceMap2000_checked fusedMap2000_checked
    DegreeTwoThreeFiniteComparisons.comparison2000
#print axioms sourceMap2000_checked
#print axioms fusedMap2000_checked
#print axioms certified2000
def sourceMap2000swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap2000swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2000swap_checked : acceptsGraphIso
    (source (graph core2000) (root 10) 2 0) DegreeTwoThreeSpectrum3787.graph sourceMap2000swap=true := by decide +kernel
theorem fusedMap2000swap_checked : acceptsGraphIso
    (fused (graph core2000) (root 10) 2 0) DegreeTwoThreeSpectrum3164.graph fusedMap2000swap=true := by decide +kernel
theorem certified2000swap : Certified (graph core2000) (root 10) 2 0 :=
  of_native_maps core2000 DegreeTwoThreeSpectrum3787.graph DegreeTwoThreeSpectrum3164.graph
    sourceMap2000swap fusedMap2000swap sourceMap2000swap_checked fusedMap2000swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2000
#print axioms sourceMap2000swap_checked
#print axioms fusedMap2000swap_checked
#print axioms certified2000swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2207 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap2207 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2207 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2207_checked : acceptsGraphIso
    (source (graph core2207) (root 8) 0 4) DegreeTwoThreeSpectrum3495.graph sourceMap2207=true := by decide +kernel
theorem fusedMap2207_checked : acceptsGraphIso
    (fused (graph core2207) (root 8) 0 4) DegreeTwoThreeSpectrum2703.graph fusedMap2207=true := by decide +kernel
theorem certified2207 : Certified (graph core2207) (root 8) 0 4 :=
  of_native_maps core2207 DegreeTwoThreeSpectrum3495.graph DegreeTwoThreeSpectrum2703.graph
    sourceMap2207 fusedMap2207 sourceMap2207_checked fusedMap2207_checked
    DegreeTwoThreeFiniteComparisons.comparison2207
#print axioms sourceMap2207_checked
#print axioms fusedMap2207_checked
#print axioms certified2207
def sourceMap2207swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2207swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2207swap_checked : acceptsGraphIso
    (source (graph core2207) (root 8) 4 0) DegreeTwoThreeSpectrum3495.graph sourceMap2207swap=true := by decide +kernel
theorem fusedMap2207swap_checked : acceptsGraphIso
    (fused (graph core2207) (root 8) 4 0) DegreeTwoThreeSpectrum2703.graph fusedMap2207swap=true := by decide +kernel
theorem certified2207swap : Certified (graph core2207) (root 8) 4 0 :=
  of_native_maps core2207 DegreeTwoThreeSpectrum3495.graph DegreeTwoThreeSpectrum2703.graph
    sourceMap2207swap fusedMap2207swap sourceMap2207swap_checked fusedMap2207swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2207
#print axioms sourceMap2207swap_checked
#print axioms fusedMap2207swap_checked
#print axioms certified2207swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

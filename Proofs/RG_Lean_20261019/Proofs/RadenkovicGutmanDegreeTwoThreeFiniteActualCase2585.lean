/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2585 : Family 10 := level10.get ⟨484,by decide⟩
def sourceMap2585 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,6,7,8,9,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2585 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2585_checked : acceptsGraphIso
    (source (graph core2585) (root 10) 0 4) DegreeTwoThreeSpectrum5924.graph sourceMap2585=true := by decide +kernel
theorem fusedMap2585_checked : acceptsGraphIso
    (fused (graph core2585) (root 10) 0 4) DegreeTwoThreeSpectrum5950.graph fusedMap2585=true := by decide +kernel
theorem certified2585 : Certified (graph core2585) (root 10) 0 4 :=
  of_native_maps core2585 DegreeTwoThreeSpectrum5924.graph DegreeTwoThreeSpectrum5950.graph
    sourceMap2585 fusedMap2585 sourceMap2585_checked fusedMap2585_checked
    DegreeTwoThreeFiniteComparisons.comparison2585
#print axioms sourceMap2585_checked
#print axioms fusedMap2585_checked
#print axioms certified2585
def sourceMap2585swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,6,7,8,1,2,3,4,5,9] (sourceLabel 10 4 0 v)
def fusedMap2585swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2585swap_checked : acceptsGraphIso
    (source (graph core2585) (root 10) 4 0) DegreeTwoThreeSpectrum5924.graph sourceMap2585swap=true := by decide +kernel
theorem fusedMap2585swap_checked : acceptsGraphIso
    (fused (graph core2585) (root 10) 4 0) DegreeTwoThreeSpectrum5950.graph fusedMap2585swap=true := by decide +kernel
theorem certified2585swap : Certified (graph core2585) (root 10) 4 0 :=
  of_native_maps core2585 DegreeTwoThreeSpectrum5924.graph DegreeTwoThreeSpectrum5950.graph
    sourceMap2585swap fusedMap2585swap sourceMap2585swap_checked fusedMap2585swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2585
#print axioms sourceMap2585swap_checked
#print axioms fusedMap2585swap_checked
#print axioms certified2585swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

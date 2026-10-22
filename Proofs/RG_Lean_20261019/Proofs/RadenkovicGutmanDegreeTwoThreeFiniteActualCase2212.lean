/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2212 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap2212 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2212 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2212_checked : acceptsGraphIso
    (source (graph core2212) (root 8) 0 4) DegreeTwoThreeSpectrum3004.graph sourceMap2212=true := by decide +kernel
theorem fusedMap2212_checked : acceptsGraphIso
    (fused (graph core2212) (root 8) 0 4) DegreeTwoThreeSpectrum3006.graph fusedMap2212=true := by decide +kernel
theorem certified2212 : Certified (graph core2212) (root 8) 0 4 :=
  of_native_maps core2212 DegreeTwoThreeSpectrum3004.graph DegreeTwoThreeSpectrum3006.graph
    sourceMap2212 fusedMap2212 sourceMap2212_checked fusedMap2212_checked
    DegreeTwoThreeFiniteComparisons.comparison2212
#print axioms sourceMap2212_checked
#print axioms fusedMap2212_checked
#print axioms certified2212
def sourceMap2212swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2212swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2212swap_checked : acceptsGraphIso
    (source (graph core2212) (root 8) 4 0) DegreeTwoThreeSpectrum3004.graph sourceMap2212swap=true := by decide +kernel
theorem fusedMap2212swap_checked : acceptsGraphIso
    (fused (graph core2212) (root 8) 4 0) DegreeTwoThreeSpectrum3006.graph fusedMap2212swap=true := by decide +kernel
theorem certified2212swap : Certified (graph core2212) (root 8) 4 0 :=
  of_native_maps core2212 DegreeTwoThreeSpectrum3004.graph DegreeTwoThreeSpectrum3006.graph
    sourceMap2212swap fusedMap2212swap sourceMap2212swap_checked fusedMap2212swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2212
#print axioms sourceMap2212swap_checked
#print axioms fusedMap2212swap_checked
#print axioms certified2212swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2565 : Family 10 := level10.get ⟨425,by decide⟩
def sourceMap2565 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2565 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2565_checked : acceptsGraphIso
    (source (graph core2565) (root 10) 0 4) DegreeTwoThreeSpectrum5812.graph sourceMap2565=true := by decide +kernel
theorem fusedMap2565_checked : acceptsGraphIso
    (fused (graph core2565) (root 10) 0 4) DegreeTwoThreeSpectrum5816.graph fusedMap2565=true := by decide +kernel
theorem certified2565 : Certified (graph core2565) (root 10) 0 4 :=
  of_native_maps core2565 DegreeTwoThreeSpectrum5812.graph DegreeTwoThreeSpectrum5816.graph
    sourceMap2565 fusedMap2565 sourceMap2565_checked fusedMap2565_checked
    DegreeTwoThreeFiniteComparisons.comparison2565
#print axioms sourceMap2565_checked
#print axioms fusedMap2565_checked
#print axioms certified2565
def sourceMap2565swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2565swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2565swap_checked : acceptsGraphIso
    (source (graph core2565) (root 10) 4 0) DegreeTwoThreeSpectrum5812.graph sourceMap2565swap=true := by decide +kernel
theorem fusedMap2565swap_checked : acceptsGraphIso
    (fused (graph core2565) (root 10) 4 0) DegreeTwoThreeSpectrum5816.graph fusedMap2565swap=true := by decide +kernel
theorem certified2565swap : Certified (graph core2565) (root 10) 4 0 :=
  of_native_maps core2565 DegreeTwoThreeSpectrum5812.graph DegreeTwoThreeSpectrum5816.graph
    sourceMap2565swap fusedMap2565swap sourceMap2565swap_checked fusedMap2565swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2565
#print axioms sourceMap2565swap_checked
#print axioms fusedMap2565swap_checked
#print axioms certified2565swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2461 : Family 10 := level10.get ⟨50,by decide⟩
def sourceMap2461 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2461 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 0 4 v)
theorem sourceMap2461_checked : acceptsGraphIso
    (source (graph core2461) (root 10) 0 4) DegreeTwoThreeSpectrum5112.graph sourceMap2461=true := by decide +kernel
theorem fusedMap2461_checked : acceptsGraphIso
    (fused (graph core2461) (root 10) 0 4) DegreeTwoThreeSpectrum5132.graph fusedMap2461=true := by decide +kernel
theorem certified2461 : Certified (graph core2461) (root 10) 0 4 :=
  of_native_maps core2461 DegreeTwoThreeSpectrum5112.graph DegreeTwoThreeSpectrum5132.graph
    sourceMap2461 fusedMap2461 sourceMap2461_checked fusedMap2461_checked
    DegreeTwoThreeFiniteComparisons.comparison2461
#print axioms sourceMap2461_checked
#print axioms fusedMap2461_checked
#print axioms certified2461
def sourceMap2461swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2461swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 4 0 v)
theorem sourceMap2461swap_checked : acceptsGraphIso
    (source (graph core2461) (root 10) 4 0) DegreeTwoThreeSpectrum5112.graph sourceMap2461swap=true := by decide +kernel
theorem fusedMap2461swap_checked : acceptsGraphIso
    (fused (graph core2461) (root 10) 4 0) DegreeTwoThreeSpectrum5132.graph fusedMap2461swap=true := by decide +kernel
theorem certified2461swap : Certified (graph core2461) (root 10) 4 0 :=
  of_native_maps core2461 DegreeTwoThreeSpectrum5112.graph DegreeTwoThreeSpectrum5132.graph
    sourceMap2461swap fusedMap2461swap sourceMap2461swap_checked fusedMap2461swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2461
#print axioms sourceMap2461swap_checked
#print axioms fusedMap2461swap_checked
#print axioms certified2461swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

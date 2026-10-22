/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2768 : Family 10 := level10.get ⟨983,by decide⟩
def sourceMap2768 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2768 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2768_checked : acceptsGraphIso
    (source (graph core2768) (root 10) 0 4) DegreeTwoThreeSpectrum7049.graph sourceMap2768=true := by decide +kernel
theorem fusedMap2768_checked : acceptsGraphIso
    (fused (graph core2768) (root 10) 0 4) DegreeTwoThreeSpectrum5919.graph fusedMap2768=true := by decide +kernel
theorem certified2768 : Certified (graph core2768) (root 10) 0 4 :=
  of_native_maps core2768 DegreeTwoThreeSpectrum7049.graph DegreeTwoThreeSpectrum5919.graph
    sourceMap2768 fusedMap2768 sourceMap2768_checked fusedMap2768_checked
    DegreeTwoThreeFiniteComparisons.comparison2768
#print axioms sourceMap2768_checked
#print axioms fusedMap2768_checked
#print axioms certified2768
def sourceMap2768swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2768swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2768swap_checked : acceptsGraphIso
    (source (graph core2768) (root 10) 4 0) DegreeTwoThreeSpectrum7049.graph sourceMap2768swap=true := by decide +kernel
theorem fusedMap2768swap_checked : acceptsGraphIso
    (fused (graph core2768) (root 10) 4 0) DegreeTwoThreeSpectrum5919.graph fusedMap2768swap=true := by decide +kernel
theorem certified2768swap : Certified (graph core2768) (root 10) 4 0 :=
  of_native_maps core2768 DegreeTwoThreeSpectrum7049.graph DegreeTwoThreeSpectrum5919.graph
    sourceMap2768swap fusedMap2768swap sourceMap2768swap_checked fusedMap2768swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2768
#print axioms sourceMap2768swap_checked
#print axioms fusedMap2768swap_checked
#print axioms certified2768swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

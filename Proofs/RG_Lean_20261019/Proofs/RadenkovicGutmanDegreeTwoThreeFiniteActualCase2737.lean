/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2737 : Family 10 := level10.get ⟨916,by decide⟩
def sourceMap2737 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2737 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2737_checked : acceptsGraphIso
    (source (graph core2737) (root 10) 0 4) DegreeTwoThreeSpectrum6988.graph sourceMap2737=true := by decide +kernel
theorem fusedMap2737_checked : acceptsGraphIso
    (fused (graph core2737) (root 10) 0 4) DegreeTwoThreeSpectrum5794.graph fusedMap2737=true := by decide +kernel
theorem certified2737 : Certified (graph core2737) (root 10) 0 4 :=
  of_native_maps core2737 DegreeTwoThreeSpectrum6988.graph DegreeTwoThreeSpectrum5794.graph
    sourceMap2737 fusedMap2737 sourceMap2737_checked fusedMap2737_checked
    DegreeTwoThreeFiniteComparisons.comparison2737
#print axioms sourceMap2737_checked
#print axioms fusedMap2737_checked
#print axioms certified2737
def sourceMap2737swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2737swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2737swap_checked : acceptsGraphIso
    (source (graph core2737) (root 10) 4 0) DegreeTwoThreeSpectrum6988.graph sourceMap2737swap=true := by decide +kernel
theorem fusedMap2737swap_checked : acceptsGraphIso
    (fused (graph core2737) (root 10) 4 0) DegreeTwoThreeSpectrum5794.graph fusedMap2737swap=true := by decide +kernel
theorem certified2737swap : Certified (graph core2737) (root 10) 4 0 :=
  of_native_maps core2737 DegreeTwoThreeSpectrum6988.graph DegreeTwoThreeSpectrum5794.graph
    sourceMap2737swap fusedMap2737swap sourceMap2737swap_checked fusedMap2737swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2737
#print axioms sourceMap2737swap_checked
#print axioms fusedMap2737swap_checked
#print axioms certified2737swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

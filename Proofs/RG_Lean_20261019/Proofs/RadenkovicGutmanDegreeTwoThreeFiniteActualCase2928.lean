/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2928 : Family 10 := level10.get ⟨1380,by decide⟩
def sourceMap2928 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2928 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2928_checked : acceptsGraphIso
    (source (graph core2928) (root 10) 0 4) DegreeTwoThreeSpectrum6731.graph sourceMap2928=true := by decide +kernel
theorem fusedMap2928_checked : acceptsGraphIso
    (fused (graph core2928) (root 10) 0 4) DegreeTwoThreeSpectrum6732.graph fusedMap2928=true := by decide +kernel
theorem certified2928 : Certified (graph core2928) (root 10) 0 4 :=
  of_native_maps core2928 DegreeTwoThreeSpectrum6731.graph DegreeTwoThreeSpectrum6732.graph
    sourceMap2928 fusedMap2928 sourceMap2928_checked fusedMap2928_checked
    DegreeTwoThreeFiniteComparisons.comparison2928
#print axioms sourceMap2928_checked
#print axioms fusedMap2928_checked
#print axioms certified2928
def sourceMap2928swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2928swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2928swap_checked : acceptsGraphIso
    (source (graph core2928) (root 10) 4 0) DegreeTwoThreeSpectrum6731.graph sourceMap2928swap=true := by decide +kernel
theorem fusedMap2928swap_checked : acceptsGraphIso
    (fused (graph core2928) (root 10) 4 0) DegreeTwoThreeSpectrum6732.graph fusedMap2928swap=true := by decide +kernel
theorem certified2928swap : Certified (graph core2928) (root 10) 4 0 :=
  of_native_maps core2928 DegreeTwoThreeSpectrum6731.graph DegreeTwoThreeSpectrum6732.graph
    sourceMap2928swap fusedMap2928swap sourceMap2928swap_checked fusedMap2928swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2928
#print axioms sourceMap2928swap_checked
#print axioms fusedMap2928swap_checked
#print axioms certified2928swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

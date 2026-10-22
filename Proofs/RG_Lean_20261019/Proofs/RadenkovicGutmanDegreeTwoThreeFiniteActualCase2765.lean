/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2765 : Family 10 := level10.get ⟨978,by decide⟩
def sourceMap2765 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2765 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2765_checked : acceptsGraphIso
    (source (graph core2765) (root 10) 0 4) DegreeTwoThreeSpectrum7044.graph sourceMap2765=true := by decide +kernel
theorem fusedMap2765_checked : acceptsGraphIso
    (fused (graph core2765) (root 10) 0 4) DegreeTwoThreeSpectrum5912.graph fusedMap2765=true := by decide +kernel
theorem certified2765 : Certified (graph core2765) (root 10) 0 4 :=
  of_native_maps core2765 DegreeTwoThreeSpectrum7044.graph DegreeTwoThreeSpectrum5912.graph
    sourceMap2765 fusedMap2765 sourceMap2765_checked fusedMap2765_checked
    DegreeTwoThreeFiniteComparisons.comparison2765
#print axioms sourceMap2765_checked
#print axioms fusedMap2765_checked
#print axioms certified2765
def sourceMap2765swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2765swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2765swap_checked : acceptsGraphIso
    (source (graph core2765) (root 10) 4 0) DegreeTwoThreeSpectrum7044.graph sourceMap2765swap=true := by decide +kernel
theorem fusedMap2765swap_checked : acceptsGraphIso
    (fused (graph core2765) (root 10) 4 0) DegreeTwoThreeSpectrum5912.graph fusedMap2765swap=true := by decide +kernel
theorem certified2765swap : Certified (graph core2765) (root 10) 4 0 :=
  of_native_maps core2765 DegreeTwoThreeSpectrum7044.graph DegreeTwoThreeSpectrum5912.graph
    sourceMap2765swap fusedMap2765swap sourceMap2765swap_checked fusedMap2765swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2765
#print axioms sourceMap2765swap_checked
#print axioms fusedMap2765swap_checked
#print axioms certified2765swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

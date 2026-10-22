/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2163 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap2163 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2163 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2163_checked : acceptsGraphIso
    (source (graph core2163) (root 8) 0 4) DegreeTwoThreeSpectrum2715.graph sourceMap2163=true := by decide +kernel
theorem fusedMap2163_checked : acceptsGraphIso
    (fused (graph core2163) (root 8) 0 4) DegreeTwoThreeSpectrum2717.graph fusedMap2163=true := by decide +kernel
theorem certified2163 : Certified (graph core2163) (root 8) 0 4 :=
  of_native_maps core2163 DegreeTwoThreeSpectrum2715.graph DegreeTwoThreeSpectrum2717.graph
    sourceMap2163 fusedMap2163 sourceMap2163_checked fusedMap2163_checked
    DegreeTwoThreeFiniteComparisons.comparison2163
#print axioms sourceMap2163_checked
#print axioms fusedMap2163_checked
#print axioms certified2163
def sourceMap2163swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2163swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2163swap_checked : acceptsGraphIso
    (source (graph core2163) (root 8) 4 0) DegreeTwoThreeSpectrum2715.graph sourceMap2163swap=true := by decide +kernel
theorem fusedMap2163swap_checked : acceptsGraphIso
    (fused (graph core2163) (root 8) 4 0) DegreeTwoThreeSpectrum2717.graph fusedMap2163swap=true := by decide +kernel
theorem certified2163swap : Certified (graph core2163) (root 8) 4 0 :=
  of_native_maps core2163 DegreeTwoThreeSpectrum2715.graph DegreeTwoThreeSpectrum2717.graph
    sourceMap2163swap fusedMap2163swap sourceMap2163swap_checked fusedMap2163swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2163
#print axioms sourceMap2163swap_checked
#print axioms fusedMap2163swap_checked
#print axioms certified2163swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

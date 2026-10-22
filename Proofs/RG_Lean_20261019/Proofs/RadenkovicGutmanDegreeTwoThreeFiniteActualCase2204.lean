/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2204 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap2204 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2204 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2204_checked : acceptsGraphIso
    (source (graph core2204) (root 8) 0 4) DegreeTwoThreeSpectrum3465.graph sourceMap2204=true := by decide +kernel
theorem fusedMap2204_checked : acceptsGraphIso
    (fused (graph core2204) (root 8) 0 4) DegreeTwoThreeSpectrum2690.graph fusedMap2204=true := by decide +kernel
theorem certified2204 : Certified (graph core2204) (root 8) 0 4 :=
  of_native_maps core2204 DegreeTwoThreeSpectrum3465.graph DegreeTwoThreeSpectrum2690.graph
    sourceMap2204 fusedMap2204 sourceMap2204_checked fusedMap2204_checked
    DegreeTwoThreeFiniteComparisons.comparison2204
#print axioms sourceMap2204_checked
#print axioms fusedMap2204_checked
#print axioms certified2204
def sourceMap2204swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2204swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2204swap_checked : acceptsGraphIso
    (source (graph core2204) (root 8) 4 0) DegreeTwoThreeSpectrum3465.graph sourceMap2204swap=true := by decide +kernel
theorem fusedMap2204swap_checked : acceptsGraphIso
    (fused (graph core2204) (root 8) 4 0) DegreeTwoThreeSpectrum2690.graph fusedMap2204swap=true := by decide +kernel
theorem certified2204swap : Certified (graph core2204) (root 8) 4 0 :=
  of_native_maps core2204 DegreeTwoThreeSpectrum3465.graph DegreeTwoThreeSpectrum2690.graph
    sourceMap2204swap fusedMap2204swap sourceMap2204swap_checked fusedMap2204swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2204
#print axioms sourceMap2204swap_checked
#print axioms fusedMap2204swap_checked
#print axioms certified2204swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

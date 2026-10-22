/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2201 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap2201 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2201 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2201_checked : acceptsGraphIso
    (source (graph core2201) (root 8) 0 4) DegreeTwoThreeSpectrum3404.graph sourceMap2201=true := by decide +kernel
theorem fusedMap2201_checked : acceptsGraphIso
    (fused (graph core2201) (root 8) 0 4) DegreeTwoThreeSpectrum2651.graph fusedMap2201=true := by decide +kernel
theorem certified2201 : Certified (graph core2201) (root 8) 0 4 :=
  of_native_maps core2201 DegreeTwoThreeSpectrum3404.graph DegreeTwoThreeSpectrum2651.graph
    sourceMap2201 fusedMap2201 sourceMap2201_checked fusedMap2201_checked
    DegreeTwoThreeFiniteComparisons.comparison2201
#print axioms sourceMap2201_checked
#print axioms fusedMap2201_checked
#print axioms certified2201
def sourceMap2201swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2201swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2201swap_checked : acceptsGraphIso
    (source (graph core2201) (root 8) 4 0) DegreeTwoThreeSpectrum3404.graph sourceMap2201swap=true := by decide +kernel
theorem fusedMap2201swap_checked : acceptsGraphIso
    (fused (graph core2201) (root 8) 4 0) DegreeTwoThreeSpectrum2651.graph fusedMap2201swap=true := by decide +kernel
theorem certified2201swap : Certified (graph core2201) (root 8) 4 0 :=
  of_native_maps core2201 DegreeTwoThreeSpectrum3404.graph DegreeTwoThreeSpectrum2651.graph
    sourceMap2201swap fusedMap2201swap sourceMap2201swap_checked fusedMap2201swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2201
#print axioms sourceMap2201swap_checked
#print axioms fusedMap2201swap_checked
#print axioms certified2201swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

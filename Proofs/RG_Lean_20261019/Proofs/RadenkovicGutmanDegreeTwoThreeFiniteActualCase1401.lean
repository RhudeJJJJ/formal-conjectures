/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1401 : Family 9 := level9.get ⟨601,by decide⟩
def sourceMap1401 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1401 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1401_checked : acceptsGraphIso
    (source (graph core1401) (root 9) 0 2) DegreeTwoThreeSpectrum2273.graph sourceMap1401=true := by decide +kernel
theorem fusedMap1401_checked : acceptsGraphIso
    (fused (graph core1401) (root 9) 0 2) DegreeTwoThreeSpectrum2007.graph fusedMap1401=true := by decide +kernel
theorem certified1401 : Certified (graph core1401) (root 9) 0 2 :=
  of_native_maps core1401 DegreeTwoThreeSpectrum2273.graph DegreeTwoThreeSpectrum2007.graph
    sourceMap1401 fusedMap1401 sourceMap1401_checked fusedMap1401_checked
    DegreeTwoThreeFiniteComparisons.comparison1401
#print axioms sourceMap1401_checked
#print axioms fusedMap1401_checked
#print axioms certified1401
def sourceMap1401swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1401swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1401swap_checked : acceptsGraphIso
    (source (graph core1401) (root 9) 2 0) DegreeTwoThreeSpectrum2273.graph sourceMap1401swap=true := by decide +kernel
theorem fusedMap1401swap_checked : acceptsGraphIso
    (fused (graph core1401) (root 9) 2 0) DegreeTwoThreeSpectrum2007.graph fusedMap1401swap=true := by decide +kernel
theorem certified1401swap : Certified (graph core1401) (root 9) 2 0 :=
  of_native_maps core1401 DegreeTwoThreeSpectrum2273.graph DegreeTwoThreeSpectrum2007.graph
    sourceMap1401swap fusedMap1401swap sourceMap1401swap_checked fusedMap1401swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1401
#print axioms sourceMap1401swap_checked
#print axioms fusedMap1401swap_checked
#print axioms certified1401swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

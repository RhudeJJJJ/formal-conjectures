/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1605 : Family 10 := level10.get ⟨619,by decide⟩
def sourceMap1605 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1605 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1605_checked : acceptsGraphIso
    (source (graph core1605) (root 10) 0 2) DegreeTwoThreeSpectrum3300.graph sourceMap1605=true := by decide +kernel
theorem fusedMap1605_checked : acceptsGraphIso
    (fused (graph core1605) (root 10) 0 2) DegreeTwoThreeSpectrum2564.graph fusedMap1605=true := by decide +kernel
theorem certified1605 : Certified (graph core1605) (root 10) 0 2 :=
  of_native_maps core1605 DegreeTwoThreeSpectrum3300.graph DegreeTwoThreeSpectrum2564.graph
    sourceMap1605 fusedMap1605 sourceMap1605_checked fusedMap1605_checked
    DegreeTwoThreeFiniteComparisons.comparison1605
#print axioms sourceMap1605_checked
#print axioms fusedMap1605_checked
#print axioms certified1605
def sourceMap1605swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1605swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1605swap_checked : acceptsGraphIso
    (source (graph core1605) (root 10) 2 0) DegreeTwoThreeSpectrum3300.graph sourceMap1605swap=true := by decide +kernel
theorem fusedMap1605swap_checked : acceptsGraphIso
    (fused (graph core1605) (root 10) 2 0) DegreeTwoThreeSpectrum2564.graph fusedMap1605swap=true := by decide +kernel
theorem certified1605swap : Certified (graph core1605) (root 10) 2 0 :=
  of_native_maps core1605 DegreeTwoThreeSpectrum3300.graph DegreeTwoThreeSpectrum2564.graph
    sourceMap1605swap fusedMap1605swap sourceMap1605swap_checked fusedMap1605swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1605
#print axioms sourceMap1605swap_checked
#print axioms fusedMap1605swap_checked
#print axioms certified1605swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1327 : Family 9 := level9.get ⟨424,by decide⟩
def sourceMap1327 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1327 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1327_checked : acceptsGraphIso
    (source (graph core1327) (root 9) 0 2) DegreeTwoThreeSpectrum2092.graph sourceMap1327=true := by decide +kernel
theorem fusedMap1327_checked : acceptsGraphIso
    (fused (graph core1327) (root 9) 0 2) DegreeTwoThreeSpectrum2094.graph fusedMap1327=true := by decide +kernel
theorem certified1327 : Certified (graph core1327) (root 9) 0 2 :=
  of_native_maps core1327 DegreeTwoThreeSpectrum2092.graph DegreeTwoThreeSpectrum2094.graph
    sourceMap1327 fusedMap1327 sourceMap1327_checked fusedMap1327_checked
    DegreeTwoThreeFiniteComparisons.comparison1327
#print axioms sourceMap1327_checked
#print axioms fusedMap1327_checked
#print axioms certified1327
def sourceMap1327swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1327swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1327swap_checked : acceptsGraphIso
    (source (graph core1327) (root 9) 2 0) DegreeTwoThreeSpectrum2092.graph sourceMap1327swap=true := by decide +kernel
theorem fusedMap1327swap_checked : acceptsGraphIso
    (fused (graph core1327) (root 9) 2 0) DegreeTwoThreeSpectrum2094.graph fusedMap1327swap=true := by decide +kernel
theorem certified1327swap : Certified (graph core1327) (root 9) 2 0 :=
  of_native_maps core1327 DegreeTwoThreeSpectrum2092.graph DegreeTwoThreeSpectrum2094.graph
    sourceMap1327swap fusedMap1327swap sourceMap1327swap_checked fusedMap1327swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1327
#print axioms sourceMap1327swap_checked
#print axioms fusedMap1327swap_checked
#print axioms certified1327swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1303 : Family 9 := level9.get ⟨364,by decide⟩
def sourceMap1303 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1303 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1303_checked : acceptsGraphIso
    (source (graph core1303) (root 9) 0 2) DegreeTwoThreeSpectrum2004.graph sourceMap1303=true := by decide +kernel
theorem fusedMap1303_checked : acceptsGraphIso
    (fused (graph core1303) (root 9) 0 2) DegreeTwoThreeSpectrum2006.graph fusedMap1303=true := by decide +kernel
theorem certified1303 : Certified (graph core1303) (root 9) 0 2 :=
  of_native_maps core1303 DegreeTwoThreeSpectrum2004.graph DegreeTwoThreeSpectrum2006.graph
    sourceMap1303 fusedMap1303 sourceMap1303_checked fusedMap1303_checked
    DegreeTwoThreeFiniteComparisons.comparison1303
#print axioms sourceMap1303_checked
#print axioms fusedMap1303_checked
#print axioms certified1303
def sourceMap1303swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1303swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1303swap_checked : acceptsGraphIso
    (source (graph core1303) (root 9) 2 0) DegreeTwoThreeSpectrum2004.graph sourceMap1303swap=true := by decide +kernel
theorem fusedMap1303swap_checked : acceptsGraphIso
    (fused (graph core1303) (root 9) 2 0) DegreeTwoThreeSpectrum2006.graph fusedMap1303swap=true := by decide +kernel
theorem certified1303swap : Certified (graph core1303) (root 9) 2 0 :=
  of_native_maps core1303 DegreeTwoThreeSpectrum2004.graph DegreeTwoThreeSpectrum2006.graph
    sourceMap1303swap fusedMap1303swap sourceMap1303swap_checked fusedMap1303swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1303
#print axioms sourceMap1303swap_checked
#print axioms fusedMap1303swap_checked
#print axioms certified1303swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

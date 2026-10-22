/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1309 : Family 9 := level9.get ⟨380,by decide⟩
def sourceMap1309 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1309 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1309_checked : acceptsGraphIso
    (source (graph core1309) (root 9) 0 2) DegreeTwoThreeSpectrum2028.graph sourceMap1309=true := by decide +kernel
theorem fusedMap1309_checked : acceptsGraphIso
    (fused (graph core1309) (root 9) 0 2) DegreeTwoThreeSpectrum2030.graph fusedMap1309=true := by decide +kernel
theorem certified1309 : Certified (graph core1309) (root 9) 0 2 :=
  of_native_maps core1309 DegreeTwoThreeSpectrum2028.graph DegreeTwoThreeSpectrum2030.graph
    sourceMap1309 fusedMap1309 sourceMap1309_checked fusedMap1309_checked
    DegreeTwoThreeFiniteComparisons.comparison1309
#print axioms sourceMap1309_checked
#print axioms fusedMap1309_checked
#print axioms certified1309
def sourceMap1309swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1309swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1309swap_checked : acceptsGraphIso
    (source (graph core1309) (root 9) 2 0) DegreeTwoThreeSpectrum2028.graph sourceMap1309swap=true := by decide +kernel
theorem fusedMap1309swap_checked : acceptsGraphIso
    (fused (graph core1309) (root 9) 2 0) DegreeTwoThreeSpectrum2030.graph fusedMap1309swap=true := by decide +kernel
theorem certified1309swap : Certified (graph core1309) (root 9) 2 0 :=
  of_native_maps core1309 DegreeTwoThreeSpectrum2028.graph DegreeTwoThreeSpectrum2030.graph
    sourceMap1309swap fusedMap1309swap sourceMap1309swap_checked fusedMap1309swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1309
#print axioms sourceMap1309swap_checked
#print axioms fusedMap1309swap_checked
#print axioms certified1309swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

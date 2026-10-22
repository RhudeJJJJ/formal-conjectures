/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1570 : Family 10 := level10.get ⟨510,by decide⟩
def sourceMap1570 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1570 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1570_checked : acceptsGraphIso
    (source (graph core1570) (root 10) 0 2) DegreeTwoThreeSpectrum3051.graph sourceMap1570=true := by decide +kernel
theorem fusedMap1570_checked : acceptsGraphIso
    (fused (graph core1570) (root 10) 0 2) DegreeTwoThreeSpectrum2447.graph fusedMap1570=true := by decide +kernel
theorem certified1570 : Certified (graph core1570) (root 10) 0 2 :=
  of_native_maps core1570 DegreeTwoThreeSpectrum3051.graph DegreeTwoThreeSpectrum2447.graph
    sourceMap1570 fusedMap1570 sourceMap1570_checked fusedMap1570_checked
    DegreeTwoThreeFiniteComparisons.comparison1570
#print axioms sourceMap1570_checked
#print axioms fusedMap1570_checked
#print axioms certified1570
def sourceMap1570swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1570swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1570swap_checked : acceptsGraphIso
    (source (graph core1570) (root 10) 2 0) DegreeTwoThreeSpectrum3051.graph sourceMap1570swap=true := by decide +kernel
theorem fusedMap1570swap_checked : acceptsGraphIso
    (fused (graph core1570) (root 10) 2 0) DegreeTwoThreeSpectrum2447.graph fusedMap1570swap=true := by decide +kernel
theorem certified1570swap : Certified (graph core1570) (root 10) 2 0 :=
  of_native_maps core1570 DegreeTwoThreeSpectrum3051.graph DegreeTwoThreeSpectrum2447.graph
    sourceMap1570swap fusedMap1570swap sourceMap1570swap_checked fusedMap1570swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1570
#print axioms sourceMap1570swap_checked
#print axioms fusedMap1570swap_checked
#print axioms certified1570swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

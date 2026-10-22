/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1573 : Family 10 := level10.get ⟨520,by decide⟩
def sourceMap1573 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1573 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1573_checked : acceptsGraphIso
    (source (graph core1573) (root 10) 0 2) DegreeTwoThreeSpectrum3080.graph sourceMap1573=true := by decide +kernel
theorem fusedMap1573_checked : acceptsGraphIso
    (fused (graph core1573) (root 10) 0 2) DegreeTwoThreeSpectrum2458.graph fusedMap1573=true := by decide +kernel
theorem certified1573 : Certified (graph core1573) (root 10) 0 2 :=
  of_native_maps core1573 DegreeTwoThreeSpectrum3080.graph DegreeTwoThreeSpectrum2458.graph
    sourceMap1573 fusedMap1573 sourceMap1573_checked fusedMap1573_checked
    DegreeTwoThreeFiniteComparisons.comparison1573
#print axioms sourceMap1573_checked
#print axioms fusedMap1573_checked
#print axioms certified1573
def sourceMap1573swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1573swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1573swap_checked : acceptsGraphIso
    (source (graph core1573) (root 10) 2 0) DegreeTwoThreeSpectrum3080.graph sourceMap1573swap=true := by decide +kernel
theorem fusedMap1573swap_checked : acceptsGraphIso
    (fused (graph core1573) (root 10) 2 0) DegreeTwoThreeSpectrum2458.graph fusedMap1573swap=true := by decide +kernel
theorem certified1573swap : Certified (graph core1573) (root 10) 2 0 :=
  of_native_maps core1573 DegreeTwoThreeSpectrum3080.graph DegreeTwoThreeSpectrum2458.graph
    sourceMap1573swap fusedMap1573swap sourceMap1573swap_checked fusedMap1573swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1573
#print axioms sourceMap1573swap_checked
#print axioms fusedMap1573swap_checked
#print axioms certified1573swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

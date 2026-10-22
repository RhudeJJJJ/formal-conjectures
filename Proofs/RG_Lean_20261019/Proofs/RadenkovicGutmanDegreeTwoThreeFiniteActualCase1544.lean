/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1544 : Family 10 := level10.get ⟨437,by decide⟩
def sourceMap1544 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1544 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1544_checked : acceptsGraphIso
    (source (graph core1544) (root 10) 0 2) DegreeTwoThreeSpectrum2902.graph sourceMap1544=true := by decide +kernel
theorem fusedMap1544_checked : acceptsGraphIso
    (fused (graph core1544) (root 10) 0 2) DegreeTwoThreeSpectrum2970.graph fusedMap1544=true := by decide +kernel
theorem certified1544 : Certified (graph core1544) (root 10) 0 2 :=
  of_native_maps core1544 DegreeTwoThreeSpectrum2902.graph DegreeTwoThreeSpectrum2970.graph
    sourceMap1544 fusedMap1544 sourceMap1544_checked fusedMap1544_checked
    DegreeTwoThreeFiniteComparisons.comparison1544
#print axioms sourceMap1544_checked
#print axioms fusedMap1544_checked
#print axioms certified1544
def sourceMap1544swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1544swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1544swap_checked : acceptsGraphIso
    (source (graph core1544) (root 10) 2 0) DegreeTwoThreeSpectrum2902.graph sourceMap1544swap=true := by decide +kernel
theorem fusedMap1544swap_checked : acceptsGraphIso
    (fused (graph core1544) (root 10) 2 0) DegreeTwoThreeSpectrum2970.graph fusedMap1544swap=true := by decide +kernel
theorem certified1544swap : Certified (graph core1544) (root 10) 2 0 :=
  of_native_maps core1544 DegreeTwoThreeSpectrum2902.graph DegreeTwoThreeSpectrum2970.graph
    sourceMap1544swap fusedMap1544swap sourceMap1544swap_checked fusedMap1544swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1544
#print axioms sourceMap1544swap_checked
#print axioms fusedMap1544swap_checked
#print axioms certified1544swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

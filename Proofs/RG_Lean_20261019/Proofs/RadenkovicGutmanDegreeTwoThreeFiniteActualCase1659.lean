/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1659 : Family 10 := level10.get ⟨774,by decide⟩
def sourceMap1659 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1659 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1659_checked : acceptsGraphIso
    (source (graph core1659) (root 10) 0 2) DegreeTwoThreeSpectrum3557.graph sourceMap1659=true := by decide +kernel
theorem fusedMap1659_checked : acceptsGraphIso
    (fused (graph core1659) (root 10) 0 2) DegreeTwoThreeSpectrum2740.graph fusedMap1659=true := by decide +kernel
theorem certified1659 : Certified (graph core1659) (root 10) 0 2 :=
  of_native_maps core1659 DegreeTwoThreeSpectrum3557.graph DegreeTwoThreeSpectrum2740.graph
    sourceMap1659 fusedMap1659 sourceMap1659_checked fusedMap1659_checked
    DegreeTwoThreeFiniteComparisons.comparison1659
#print axioms sourceMap1659_checked
#print axioms fusedMap1659_checked
#print axioms certified1659
def sourceMap1659swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1659swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1659swap_checked : acceptsGraphIso
    (source (graph core1659) (root 10) 2 0) DegreeTwoThreeSpectrum3557.graph sourceMap1659swap=true := by decide +kernel
theorem fusedMap1659swap_checked : acceptsGraphIso
    (fused (graph core1659) (root 10) 2 0) DegreeTwoThreeSpectrum2740.graph fusedMap1659swap=true := by decide +kernel
theorem certified1659swap : Certified (graph core1659) (root 10) 2 0 :=
  of_native_maps core1659 DegreeTwoThreeSpectrum3557.graph DegreeTwoThreeSpectrum2740.graph
    sourceMap1659swap fusedMap1659swap sourceMap1659swap_checked fusedMap1659swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1659
#print axioms sourceMap1659swap_checked
#print axioms fusedMap1659swap_checked
#print axioms certified1659swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1533 : Family 10 := level10.get ⟨401,by decide⟩
def sourceMap1533 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1533 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1533_checked : acceptsGraphIso
    (source (graph core1533) (root 10) 0 2) DegreeTwoThreeSpectrum2850.graph sourceMap1533=true := by decide +kernel
theorem fusedMap1533_checked : acceptsGraphIso
    (fused (graph core1533) (root 10) 0 2) DegreeTwoThreeSpectrum2904.graph fusedMap1533=true := by decide +kernel
theorem certified1533 : Certified (graph core1533) (root 10) 0 2 :=
  of_native_maps core1533 DegreeTwoThreeSpectrum2850.graph DegreeTwoThreeSpectrum2904.graph
    sourceMap1533 fusedMap1533 sourceMap1533_checked fusedMap1533_checked
    DegreeTwoThreeFiniteComparisons.comparison1533
#print axioms sourceMap1533_checked
#print axioms fusedMap1533_checked
#print axioms certified1533
def sourceMap1533swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1533swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1533swap_checked : acceptsGraphIso
    (source (graph core1533) (root 10) 2 0) DegreeTwoThreeSpectrum2850.graph sourceMap1533swap=true := by decide +kernel
theorem fusedMap1533swap_checked : acceptsGraphIso
    (fused (graph core1533) (root 10) 2 0) DegreeTwoThreeSpectrum2904.graph fusedMap1533swap=true := by decide +kernel
theorem certified1533swap : Certified (graph core1533) (root 10) 2 0 :=
  of_native_maps core1533 DegreeTwoThreeSpectrum2850.graph DegreeTwoThreeSpectrum2904.graph
    sourceMap1533swap fusedMap1533swap sourceMap1533swap_checked fusedMap1533swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1533
#print axioms sourceMap1533swap_checked
#print axioms fusedMap1533swap_checked
#print axioms certified1533swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

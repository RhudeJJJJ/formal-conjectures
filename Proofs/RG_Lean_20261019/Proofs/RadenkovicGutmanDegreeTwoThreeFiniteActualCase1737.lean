/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1737 : Family 10 := level10.get ⟨968,by decide⟩
def sourceMap1737 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1737 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,5,6,7,8,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1737_checked : acceptsGraphIso
    (source (graph core1737) (root 10) 0 2) DegreeTwoThreeSpectrum3538.graph sourceMap1737=true := by decide +kernel
theorem fusedMap1737_checked : acceptsGraphIso
    (fused (graph core1737) (root 10) 0 2) DegreeTwoThreeSpectrum2952.graph fusedMap1737=true := by decide +kernel
theorem certified1737 : Certified (graph core1737) (root 10) 0 2 :=
  of_native_maps core1737 DegreeTwoThreeSpectrum3538.graph DegreeTwoThreeSpectrum2952.graph
    sourceMap1737 fusedMap1737 sourceMap1737_checked fusedMap1737_checked
    DegreeTwoThreeFiniteComparisons.comparison1737
#print axioms sourceMap1737_checked
#print axioms fusedMap1737_checked
#print axioms certified1737
def sourceMap1737swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1737swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,5,6,7,8,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1737swap_checked : acceptsGraphIso
    (source (graph core1737) (root 10) 2 0) DegreeTwoThreeSpectrum3538.graph sourceMap1737swap=true := by decide +kernel
theorem fusedMap1737swap_checked : acceptsGraphIso
    (fused (graph core1737) (root 10) 2 0) DegreeTwoThreeSpectrum2952.graph fusedMap1737swap=true := by decide +kernel
theorem certified1737swap : Certified (graph core1737) (root 10) 2 0 :=
  of_native_maps core1737 DegreeTwoThreeSpectrum3538.graph DegreeTwoThreeSpectrum2952.graph
    sourceMap1737swap fusedMap1737swap sourceMap1737swap_checked fusedMap1737swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1737
#print axioms sourceMap1737swap_checked
#print axioms fusedMap1737swap_checked
#print axioms certified1737swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

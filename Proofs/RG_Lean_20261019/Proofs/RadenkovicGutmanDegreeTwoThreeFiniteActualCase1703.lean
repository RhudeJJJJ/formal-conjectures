/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1703 : Family 10 := level10.get ⟨889,by decide⟩
def sourceMap1703 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1703 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1703_checked : acceptsGraphIso
    (source (graph core1703) (root 10) 0 2) DegreeTwoThreeSpectrum3680.graph sourceMap1703=true := by decide +kernel
theorem fusedMap1703_checked : acceptsGraphIso
    (fused (graph core1703) (root 10) 0 2) DegreeTwoThreeSpectrum2892.graph fusedMap1703=true := by decide +kernel
theorem certified1703 : Certified (graph core1703) (root 10) 0 2 :=
  of_native_maps core1703 DegreeTwoThreeSpectrum3680.graph DegreeTwoThreeSpectrum2892.graph
    sourceMap1703 fusedMap1703 sourceMap1703_checked fusedMap1703_checked
    DegreeTwoThreeFiniteComparisons.comparison1703
#print axioms sourceMap1703_checked
#print axioms fusedMap1703_checked
#print axioms certified1703
def sourceMap1703swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1703swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1703swap_checked : acceptsGraphIso
    (source (graph core1703) (root 10) 2 0) DegreeTwoThreeSpectrum3680.graph sourceMap1703swap=true := by decide +kernel
theorem fusedMap1703swap_checked : acceptsGraphIso
    (fused (graph core1703) (root 10) 2 0) DegreeTwoThreeSpectrum2892.graph fusedMap1703swap=true := by decide +kernel
theorem certified1703swap : Certified (graph core1703) (root 10) 2 0 :=
  of_native_maps core1703 DegreeTwoThreeSpectrum3680.graph DegreeTwoThreeSpectrum2892.graph
    sourceMap1703swap fusedMap1703swap sourceMap1703swap_checked fusedMap1703swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1703
#print axioms sourceMap1703swap_checked
#print axioms fusedMap1703swap_checked
#print axioms certified1703swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

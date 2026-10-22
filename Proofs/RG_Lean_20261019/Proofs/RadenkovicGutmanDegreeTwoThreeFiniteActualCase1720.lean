/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1720 : Family 10 := level10.get ⟨934,by decide⟩
def sourceMap1720 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1720 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1720_checked : acceptsGraphIso
    (source (graph core1720) (root 10) 0 2) DegreeTwoThreeSpectrum3709.graph sourceMap1720=true := by decide +kernel
theorem fusedMap1720_checked : acceptsGraphIso
    (fused (graph core1720) (root 10) 0 2) DegreeTwoThreeSpectrum2952.graph fusedMap1720=true := by decide +kernel
theorem certified1720 : Certified (graph core1720) (root 10) 0 2 :=
  of_native_maps core1720 DegreeTwoThreeSpectrum3709.graph DegreeTwoThreeSpectrum2952.graph
    sourceMap1720 fusedMap1720 sourceMap1720_checked fusedMap1720_checked
    DegreeTwoThreeFiniteComparisons.comparison1720
#print axioms sourceMap1720_checked
#print axioms fusedMap1720_checked
#print axioms certified1720
def sourceMap1720swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1720swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1720swap_checked : acceptsGraphIso
    (source (graph core1720) (root 10) 2 0) DegreeTwoThreeSpectrum3709.graph sourceMap1720swap=true := by decide +kernel
theorem fusedMap1720swap_checked : acceptsGraphIso
    (fused (graph core1720) (root 10) 2 0) DegreeTwoThreeSpectrum2952.graph fusedMap1720swap=true := by decide +kernel
theorem certified1720swap : Certified (graph core1720) (root 10) 2 0 :=
  of_native_maps core1720 DegreeTwoThreeSpectrum3709.graph DegreeTwoThreeSpectrum2952.graph
    sourceMap1720swap fusedMap1720swap sourceMap1720swap_checked fusedMap1720swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1720
#print axioms sourceMap1720swap_checked
#print axioms fusedMap1720swap_checked
#print axioms certified1720swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

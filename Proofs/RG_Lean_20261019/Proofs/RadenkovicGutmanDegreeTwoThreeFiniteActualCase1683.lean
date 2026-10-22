/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1683 : Family 10 := level10.get ⟨836,by decide⟩
def sourceMap1683 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1683 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1683_checked : acceptsGraphIso
    (source (graph core1683) (root 10) 0 2) DegreeTwoThreeSpectrum3632.graph sourceMap1683=true := by decide +kernel
theorem fusedMap1683_checked : acceptsGraphIso
    (fused (graph core1683) (root 10) 0 2) DegreeTwoThreeSpectrum2821.graph fusedMap1683=true := by decide +kernel
theorem certified1683 : Certified (graph core1683) (root 10) 0 2 :=
  of_native_maps core1683 DegreeTwoThreeSpectrum3632.graph DegreeTwoThreeSpectrum2821.graph
    sourceMap1683 fusedMap1683 sourceMap1683_checked fusedMap1683_checked
    DegreeTwoThreeFiniteComparisons.comparison1683
#print axioms sourceMap1683_checked
#print axioms fusedMap1683_checked
#print axioms certified1683
def sourceMap1683swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1683swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1683swap_checked : acceptsGraphIso
    (source (graph core1683) (root 10) 2 0) DegreeTwoThreeSpectrum3632.graph sourceMap1683swap=true := by decide +kernel
theorem fusedMap1683swap_checked : acceptsGraphIso
    (fused (graph core1683) (root 10) 2 0) DegreeTwoThreeSpectrum2821.graph fusedMap1683swap=true := by decide +kernel
theorem certified1683swap : Certified (graph core1683) (root 10) 2 0 :=
  of_native_maps core1683 DegreeTwoThreeSpectrum3632.graph DegreeTwoThreeSpectrum2821.graph
    sourceMap1683swap fusedMap1683swap sourceMap1683swap_checked fusedMap1683swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1683
#print axioms sourceMap1683swap_checked
#print axioms fusedMap1683swap_checked
#print axioms certified1683swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

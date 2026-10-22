/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1722 : Family 10 := level10.get ⟨938,by decide⟩
def sourceMap1722 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1722 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1722_checked : acceptsGraphIso
    (source (graph core1722) (root 10) 0 2) DegreeTwoThreeSpectrum3683.graph sourceMap1722=true := by decide +kernel
theorem fusedMap1722_checked : acceptsGraphIso
    (fused (graph core1722) (root 10) 0 2) DegreeTwoThreeSpectrum2957.graph fusedMap1722=true := by decide +kernel
theorem certified1722 : Certified (graph core1722) (root 10) 0 2 :=
  of_native_maps core1722 DegreeTwoThreeSpectrum3683.graph DegreeTwoThreeSpectrum2957.graph
    sourceMap1722 fusedMap1722 sourceMap1722_checked fusedMap1722_checked
    DegreeTwoThreeFiniteComparisons.comparison1722
#print axioms sourceMap1722_checked
#print axioms fusedMap1722_checked
#print axioms certified1722
def sourceMap1722swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1722swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1722swap_checked : acceptsGraphIso
    (source (graph core1722) (root 10) 2 0) DegreeTwoThreeSpectrum3683.graph sourceMap1722swap=true := by decide +kernel
theorem fusedMap1722swap_checked : acceptsGraphIso
    (fused (graph core1722) (root 10) 2 0) DegreeTwoThreeSpectrum2957.graph fusedMap1722swap=true := by decide +kernel
theorem certified1722swap : Certified (graph core1722) (root 10) 2 0 :=
  of_native_maps core1722 DegreeTwoThreeSpectrum3683.graph DegreeTwoThreeSpectrum2957.graph
    sourceMap1722swap fusedMap1722swap sourceMap1722swap_checked fusedMap1722swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1722
#print axioms sourceMap1722swap_checked
#print axioms fusedMap1722swap_checked
#print axioms certified1722swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

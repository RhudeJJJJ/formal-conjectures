/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1747 : Family 10 := level10.get ⟨988,by decide⟩
def sourceMap1747 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,5,6,7,8,9,10,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1747 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1747_checked : acceptsGraphIso
    (source (graph core1747) (root 10) 0 2) DegreeTwoThreeSpectrum3638.graph sourceMap1747=true := by decide +kernel
theorem fusedMap1747_checked : acceptsGraphIso
    (fused (graph core1747) (root 10) 0 2) DegreeTwoThreeSpectrum2961.graph fusedMap1747=true := by decide +kernel
theorem certified1747 : Certified (graph core1747) (root 10) 0 2 :=
  of_native_maps core1747 DegreeTwoThreeSpectrum3638.graph DegreeTwoThreeSpectrum2961.graph
    sourceMap1747 fusedMap1747 sourceMap1747_checked fusedMap1747_checked
    DegreeTwoThreeFiniteComparisons.comparison1747
#print axioms sourceMap1747_checked
#print axioms fusedMap1747_checked
#print axioms certified1747
def sourceMap1747swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,5,6,7,8,9,2,3,4,10] (sourceLabel 10 2 0 v)
def fusedMap1747swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1747swap_checked : acceptsGraphIso
    (source (graph core1747) (root 10) 2 0) DegreeTwoThreeSpectrum3638.graph sourceMap1747swap=true := by decide +kernel
theorem fusedMap1747swap_checked : acceptsGraphIso
    (fused (graph core1747) (root 10) 2 0) DegreeTwoThreeSpectrum2961.graph fusedMap1747swap=true := by decide +kernel
theorem certified1747swap : Certified (graph core1747) (root 10) 2 0 :=
  of_native_maps core1747 DegreeTwoThreeSpectrum3638.graph DegreeTwoThreeSpectrum2961.graph
    sourceMap1747swap fusedMap1747swap sourceMap1747swap_checked fusedMap1747swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1747
#print axioms sourceMap1747swap_checked
#print axioms fusedMap1747swap_checked
#print axioms certified1747swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

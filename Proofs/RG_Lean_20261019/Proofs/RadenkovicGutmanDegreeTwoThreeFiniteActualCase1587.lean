/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1587 : Family 10 := level10.get ⟨562,by decide⟩
def sourceMap1587 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1587 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1587_checked : acceptsGraphIso
    (source (graph core1587) (root 10) 0 2) DegreeTwoThreeSpectrum3169.graph sourceMap1587=true := by decide +kernel
theorem fusedMap1587_checked : acceptsGraphIso
    (fused (graph core1587) (root 10) 0 2) DegreeTwoThreeSpectrum2504.graph fusedMap1587=true := by decide +kernel
theorem certified1587 : Certified (graph core1587) (root 10) 0 2 :=
  of_native_maps core1587 DegreeTwoThreeSpectrum3169.graph DegreeTwoThreeSpectrum2504.graph
    sourceMap1587 fusedMap1587 sourceMap1587_checked fusedMap1587_checked
    DegreeTwoThreeFiniteComparisons.comparison1587
#print axioms sourceMap1587_checked
#print axioms fusedMap1587_checked
#print axioms certified1587
def sourceMap1587swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1587swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1587swap_checked : acceptsGraphIso
    (source (graph core1587) (root 10) 2 0) DegreeTwoThreeSpectrum3169.graph sourceMap1587swap=true := by decide +kernel
theorem fusedMap1587swap_checked : acceptsGraphIso
    (fused (graph core1587) (root 10) 2 0) DegreeTwoThreeSpectrum2504.graph fusedMap1587swap=true := by decide +kernel
theorem certified1587swap : Certified (graph core1587) (root 10) 2 0 :=
  of_native_maps core1587 DegreeTwoThreeSpectrum3169.graph DegreeTwoThreeSpectrum2504.graph
    sourceMap1587swap fusedMap1587swap sourceMap1587swap_checked fusedMap1587swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1587
#print axioms sourceMap1587swap_checked
#print axioms fusedMap1587swap_checked
#print axioms certified1587swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

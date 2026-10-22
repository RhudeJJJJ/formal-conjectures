/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1588 : Family 10 := level10.get ⟨567,by decide⟩
def sourceMap1588 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1588 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1588_checked : acceptsGraphIso
    (source (graph core1588) (root 10) 0 2) DegreeTwoThreeSpectrum3185.graph sourceMap1588=true := by decide +kernel
theorem fusedMap1588_checked : acceptsGraphIso
    (fused (graph core1588) (root 10) 0 2) DegreeTwoThreeSpectrum2508.graph fusedMap1588=true := by decide +kernel
theorem certified1588 : Certified (graph core1588) (root 10) 0 2 :=
  of_native_maps core1588 DegreeTwoThreeSpectrum3185.graph DegreeTwoThreeSpectrum2508.graph
    sourceMap1588 fusedMap1588 sourceMap1588_checked fusedMap1588_checked
    DegreeTwoThreeFiniteComparisons.comparison1588
#print axioms sourceMap1588_checked
#print axioms fusedMap1588_checked
#print axioms certified1588
def sourceMap1588swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1588swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1588swap_checked : acceptsGraphIso
    (source (graph core1588) (root 10) 2 0) DegreeTwoThreeSpectrum3185.graph sourceMap1588swap=true := by decide +kernel
theorem fusedMap1588swap_checked : acceptsGraphIso
    (fused (graph core1588) (root 10) 2 0) DegreeTwoThreeSpectrum2508.graph fusedMap1588swap=true := by decide +kernel
theorem certified1588swap : Certified (graph core1588) (root 10) 2 0 :=
  of_native_maps core1588 DegreeTwoThreeSpectrum3185.graph DegreeTwoThreeSpectrum2508.graph
    sourceMap1588swap fusedMap1588swap sourceMap1588swap_checked fusedMap1588swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1588
#print axioms sourceMap1588swap_checked
#print axioms fusedMap1588swap_checked
#print axioms certified1588swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

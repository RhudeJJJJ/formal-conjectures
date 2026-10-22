/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1578 : Family 10 := level10.get ⟨538,by decide⟩
def sourceMap1578 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1578 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1578_checked : acceptsGraphIso
    (source (graph core1578) (root 10) 0 2) DegreeTwoThreeSpectrum3130.graph sourceMap1578=true := by decide +kernel
theorem fusedMap1578_checked : acceptsGraphIso
    (fused (graph core1578) (root 10) 0 2) DegreeTwoThreeSpectrum2476.graph fusedMap1578=true := by decide +kernel
theorem certified1578 : Certified (graph core1578) (root 10) 0 2 :=
  of_native_maps core1578 DegreeTwoThreeSpectrum3130.graph DegreeTwoThreeSpectrum2476.graph
    sourceMap1578 fusedMap1578 sourceMap1578_checked fusedMap1578_checked
    DegreeTwoThreeFiniteComparisons.comparison1578
#print axioms sourceMap1578_checked
#print axioms fusedMap1578_checked
#print axioms certified1578
def sourceMap1578swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1578swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1578swap_checked : acceptsGraphIso
    (source (graph core1578) (root 10) 2 0) DegreeTwoThreeSpectrum3130.graph sourceMap1578swap=true := by decide +kernel
theorem fusedMap1578swap_checked : acceptsGraphIso
    (fused (graph core1578) (root 10) 2 0) DegreeTwoThreeSpectrum2476.graph fusedMap1578swap=true := by decide +kernel
theorem certified1578swap : Certified (graph core1578) (root 10) 2 0 :=
  of_native_maps core1578 DegreeTwoThreeSpectrum3130.graph DegreeTwoThreeSpectrum2476.graph
    sourceMap1578swap fusedMap1578swap sourceMap1578swap_checked fusedMap1578swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1578
#print axioms sourceMap1578swap_checked
#print axioms fusedMap1578swap_checked
#print axioms certified1578swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

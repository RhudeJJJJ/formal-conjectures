/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1651 : Family 10 := level10.get ⟨749,by decide⟩
def sourceMap1651 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1651 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1651_checked : acceptsGraphIso
    (source (graph core1651) (root 10) 0 2) DegreeTwoThreeSpectrum3511.graph sourceMap1651=true := by decide +kernel
theorem fusedMap1651_checked : acceptsGraphIso
    (fused (graph core1651) (root 10) 0 2) DegreeTwoThreeSpectrum2713.graph fusedMap1651=true := by decide +kernel
theorem certified1651 : Certified (graph core1651) (root 10) 0 2 :=
  of_native_maps core1651 DegreeTwoThreeSpectrum3511.graph DegreeTwoThreeSpectrum2713.graph
    sourceMap1651 fusedMap1651 sourceMap1651_checked fusedMap1651_checked
    DegreeTwoThreeFiniteComparisons.comparison1651
#print axioms sourceMap1651_checked
#print axioms fusedMap1651_checked
#print axioms certified1651
def sourceMap1651swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1651swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1651swap_checked : acceptsGraphIso
    (source (graph core1651) (root 10) 2 0) DegreeTwoThreeSpectrum3511.graph sourceMap1651swap=true := by decide +kernel
theorem fusedMap1651swap_checked : acceptsGraphIso
    (fused (graph core1651) (root 10) 2 0) DegreeTwoThreeSpectrum2713.graph fusedMap1651swap=true := by decide +kernel
theorem certified1651swap : Certified (graph core1651) (root 10) 2 0 :=
  of_native_maps core1651 DegreeTwoThreeSpectrum3511.graph DegreeTwoThreeSpectrum2713.graph
    sourceMap1651swap fusedMap1651swap sourceMap1651swap_checked fusedMap1651swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1651
#print axioms sourceMap1651swap_checked
#print axioms fusedMap1651swap_checked
#print axioms certified1651swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1733 : Family 10 := level10.get ⟨962,by decide⟩
def sourceMap1733 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1733 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1733_checked : acceptsGraphIso
    (source (graph core1733) (root 10) 0 2) DegreeTwoThreeSpectrum3629.graph sourceMap1733=true := by decide +kernel
theorem fusedMap1733_checked : acceptsGraphIso
    (fused (graph core1733) (root 10) 0 2) DegreeTwoThreeSpectrum2958.graph fusedMap1733=true := by decide +kernel
theorem certified1733 : Certified (graph core1733) (root 10) 0 2 :=
  of_native_maps core1733 DegreeTwoThreeSpectrum3629.graph DegreeTwoThreeSpectrum2958.graph
    sourceMap1733 fusedMap1733 sourceMap1733_checked fusedMap1733_checked
    DegreeTwoThreeFiniteComparisons.comparison1733
#print axioms sourceMap1733_checked
#print axioms fusedMap1733_checked
#print axioms certified1733
def sourceMap1733swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1733swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1733swap_checked : acceptsGraphIso
    (source (graph core1733) (root 10) 2 0) DegreeTwoThreeSpectrum3629.graph sourceMap1733swap=true := by decide +kernel
theorem fusedMap1733swap_checked : acceptsGraphIso
    (fused (graph core1733) (root 10) 2 0) DegreeTwoThreeSpectrum2958.graph fusedMap1733swap=true := by decide +kernel
theorem certified1733swap : Certified (graph core1733) (root 10) 2 0 :=
  of_native_maps core1733 DegreeTwoThreeSpectrum3629.graph DegreeTwoThreeSpectrum2958.graph
    sourceMap1733swap fusedMap1733swap sourceMap1733swap_checked fusedMap1733swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1733
#print axioms sourceMap1733swap_checked
#print axioms fusedMap1733swap_checked
#print axioms certified1733swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

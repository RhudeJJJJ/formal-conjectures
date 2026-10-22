/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1781 : Family 10 := level10.get ⟨1085,by decide⟩
def sourceMap1781 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1781 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1781_checked : acceptsGraphIso
    (source (graph core1781) (root 10) 0 2) DegreeTwoThreeSpectrum3155.graph sourceMap1781=true := by decide +kernel
theorem fusedMap1781_checked : acceptsGraphIso
    (fused (graph core1781) (root 10) 0 2) DegreeTwoThreeSpectrum3152.graph fusedMap1781=true := by decide +kernel
theorem certified1781 : Certified (graph core1781) (root 10) 0 2 :=
  of_native_maps core1781 DegreeTwoThreeSpectrum3155.graph DegreeTwoThreeSpectrum3152.graph
    sourceMap1781 fusedMap1781 sourceMap1781_checked fusedMap1781_checked
    DegreeTwoThreeFiniteComparisons.comparison1781
#print axioms sourceMap1781_checked
#print axioms fusedMap1781_checked
#print axioms certified1781
def sourceMap1781swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1781swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1781swap_checked : acceptsGraphIso
    (source (graph core1781) (root 10) 2 0) DegreeTwoThreeSpectrum3155.graph sourceMap1781swap=true := by decide +kernel
theorem fusedMap1781swap_checked : acceptsGraphIso
    (fused (graph core1781) (root 10) 2 0) DegreeTwoThreeSpectrum3152.graph fusedMap1781swap=true := by decide +kernel
theorem certified1781swap : Certified (graph core1781) (root 10) 2 0 :=
  of_native_maps core1781 DegreeTwoThreeSpectrum3155.graph DegreeTwoThreeSpectrum3152.graph
    sourceMap1781swap fusedMap1781swap sourceMap1781swap_checked fusedMap1781swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1781
#print axioms sourceMap1781swap_checked
#print axioms fusedMap1781swap_checked
#print axioms certified1781swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

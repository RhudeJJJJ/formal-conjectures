/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1993 : Family 10 := level10.get ⟨1602,by decide⟩
def sourceMap1993 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1993 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1993_checked : acceptsGraphIso
    (source (graph core1993) (root 10) 0 2) DegreeTwoThreeSpectrum3778.graph sourceMap1993=true := by decide +kernel
theorem fusedMap1993_checked : acceptsGraphIso
    (fused (graph core1993) (root 10) 0 2) DegreeTwoThreeSpectrum3114.graph fusedMap1993=true := by decide +kernel
theorem certified1993 : Certified (graph core1993) (root 10) 0 2 :=
  of_native_maps core1993 DegreeTwoThreeSpectrum3778.graph DegreeTwoThreeSpectrum3114.graph
    sourceMap1993 fusedMap1993 sourceMap1993_checked fusedMap1993_checked
    DegreeTwoThreeFiniteComparisons.comparison1993
#print axioms sourceMap1993_checked
#print axioms fusedMap1993_checked
#print axioms certified1993
def sourceMap1993swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1993swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1993swap_checked : acceptsGraphIso
    (source (graph core1993) (root 10) 2 0) DegreeTwoThreeSpectrum3778.graph sourceMap1993swap=true := by decide +kernel
theorem fusedMap1993swap_checked : acceptsGraphIso
    (fused (graph core1993) (root 10) 2 0) DegreeTwoThreeSpectrum3114.graph fusedMap1993swap=true := by decide +kernel
theorem certified1993swap : Certified (graph core1993) (root 10) 2 0 :=
  of_native_maps core1993 DegreeTwoThreeSpectrum3778.graph DegreeTwoThreeSpectrum3114.graph
    sourceMap1993swap fusedMap1993swap sourceMap1993swap_checked fusedMap1993swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1993
#print axioms sourceMap1993swap_checked
#print axioms fusedMap1993swap_checked
#print axioms certified1993swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

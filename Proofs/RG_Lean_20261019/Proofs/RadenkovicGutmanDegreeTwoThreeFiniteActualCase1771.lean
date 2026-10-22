/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1771 : Family 10 := level10.get ⟨1061,by decide⟩
def sourceMap1771 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1771 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1771_checked : acceptsGraphIso
    (source (graph core1771) (root 10) 0 2) DegreeTwoThreeSpectrum3106.graph sourceMap1771=true := by decide +kernel
theorem fusedMap1771_checked : acceptsGraphIso
    (fused (graph core1771) (root 10) 0 2) DegreeTwoThreeSpectrum3110.graph fusedMap1771=true := by decide +kernel
theorem certified1771 : Certified (graph core1771) (root 10) 0 2 :=
  of_native_maps core1771 DegreeTwoThreeSpectrum3106.graph DegreeTwoThreeSpectrum3110.graph
    sourceMap1771 fusedMap1771 sourceMap1771_checked fusedMap1771_checked
    DegreeTwoThreeFiniteComparisons.comparison1771
#print axioms sourceMap1771_checked
#print axioms fusedMap1771_checked
#print axioms certified1771
def sourceMap1771swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1771swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1771swap_checked : acceptsGraphIso
    (source (graph core1771) (root 10) 2 0) DegreeTwoThreeSpectrum3106.graph sourceMap1771swap=true := by decide +kernel
theorem fusedMap1771swap_checked : acceptsGraphIso
    (fused (graph core1771) (root 10) 2 0) DegreeTwoThreeSpectrum3110.graph fusedMap1771swap=true := by decide +kernel
theorem certified1771swap : Certified (graph core1771) (root 10) 2 0 :=
  of_native_maps core1771 DegreeTwoThreeSpectrum3106.graph DegreeTwoThreeSpectrum3110.graph
    sourceMap1771swap fusedMap1771swap sourceMap1771swap_checked fusedMap1771swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1771
#print axioms sourceMap1771swap_checked
#print axioms fusedMap1771swap_checked
#print axioms certified1771swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

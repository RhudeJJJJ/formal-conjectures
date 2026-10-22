/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1825 : Family 10 := level10.get ⟨1197,by decide⟩
def sourceMap1825 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1825 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1825_checked : acceptsGraphIso
    (source (graph core1825) (root 10) 0 2) DegreeTwoThreeSpectrum3314.graph sourceMap1825=true := by decide +kernel
theorem fusedMap1825_checked : acceptsGraphIso
    (fused (graph core1825) (root 10) 0 2) DegreeTwoThreeSpectrum3315.graph fusedMap1825=true := by decide +kernel
theorem certified1825 : Certified (graph core1825) (root 10) 0 2 :=
  of_native_maps core1825 DegreeTwoThreeSpectrum3314.graph DegreeTwoThreeSpectrum3315.graph
    sourceMap1825 fusedMap1825 sourceMap1825_checked fusedMap1825_checked
    DegreeTwoThreeFiniteComparisons.comparison1825
#print axioms sourceMap1825_checked
#print axioms fusedMap1825_checked
#print axioms certified1825
def sourceMap1825swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1825swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1825swap_checked : acceptsGraphIso
    (source (graph core1825) (root 10) 2 0) DegreeTwoThreeSpectrum3314.graph sourceMap1825swap=true := by decide +kernel
theorem fusedMap1825swap_checked : acceptsGraphIso
    (fused (graph core1825) (root 10) 2 0) DegreeTwoThreeSpectrum3315.graph fusedMap1825swap=true := by decide +kernel
theorem certified1825swap : Certified (graph core1825) (root 10) 2 0 :=
  of_native_maps core1825 DegreeTwoThreeSpectrum3314.graph DegreeTwoThreeSpectrum3315.graph
    sourceMap1825swap fusedMap1825swap sourceMap1825swap_checked fusedMap1825swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1825
#print axioms sourceMap1825swap_checked
#print axioms fusedMap1825swap_checked
#print axioms certified1825swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

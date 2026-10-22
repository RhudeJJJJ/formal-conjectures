/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1778 : Family 10 := level10.get ⟨1079,by decide⟩
def sourceMap1778 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1778 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1778_checked : acceptsGraphIso
    (source (graph core1778) (root 10) 0 2) DegreeTwoThreeSpectrum3134.graph sourceMap1778=true := by decide +kernel
theorem fusedMap1778_checked : acceptsGraphIso
    (fused (graph core1778) (root 10) 0 2) DegreeTwoThreeSpectrum3136.graph fusedMap1778=true := by decide +kernel
theorem certified1778 : Certified (graph core1778) (root 10) 0 2 :=
  of_native_maps core1778 DegreeTwoThreeSpectrum3134.graph DegreeTwoThreeSpectrum3136.graph
    sourceMap1778 fusedMap1778 sourceMap1778_checked fusedMap1778_checked
    DegreeTwoThreeFiniteComparisons.comparison1778
#print axioms sourceMap1778_checked
#print axioms fusedMap1778_checked
#print axioms certified1778
def sourceMap1778swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1778swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1778swap_checked : acceptsGraphIso
    (source (graph core1778) (root 10) 2 0) DegreeTwoThreeSpectrum3134.graph sourceMap1778swap=true := by decide +kernel
theorem fusedMap1778swap_checked : acceptsGraphIso
    (fused (graph core1778) (root 10) 2 0) DegreeTwoThreeSpectrum3136.graph fusedMap1778swap=true := by decide +kernel
theorem certified1778swap : Certified (graph core1778) (root 10) 2 0 :=
  of_native_maps core1778 DegreeTwoThreeSpectrum3134.graph DegreeTwoThreeSpectrum3136.graph
    sourceMap1778swap fusedMap1778swap sourceMap1778swap_checked fusedMap1778swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1778
#print axioms sourceMap1778swap_checked
#print axioms fusedMap1778swap_checked
#print axioms certified1778swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

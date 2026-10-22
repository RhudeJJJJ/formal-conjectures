/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1937 : Family 10 := level10.get ⟨1459,by decide⟩
def sourceMap1937 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1937 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1937_checked : acceptsGraphIso
    (source (graph core1937) (root 10) 0 2) DegreeTwoThreeSpectrum3694.graph sourceMap1937=true := by decide +kernel
theorem fusedMap1937_checked : acceptsGraphIso
    (fused (graph core1937) (root 10) 0 2) DegreeTwoThreeSpectrum3695.graph fusedMap1937=true := by decide +kernel
theorem certified1937 : Certified (graph core1937) (root 10) 0 2 :=
  of_native_maps core1937 DegreeTwoThreeSpectrum3694.graph DegreeTwoThreeSpectrum3695.graph
    sourceMap1937 fusedMap1937 sourceMap1937_checked fusedMap1937_checked
    DegreeTwoThreeFiniteComparisons.comparison1937
#print axioms sourceMap1937_checked
#print axioms fusedMap1937_checked
#print axioms certified1937
def sourceMap1937swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1937swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1937swap_checked : acceptsGraphIso
    (source (graph core1937) (root 10) 2 0) DegreeTwoThreeSpectrum3694.graph sourceMap1937swap=true := by decide +kernel
theorem fusedMap1937swap_checked : acceptsGraphIso
    (fused (graph core1937) (root 10) 2 0) DegreeTwoThreeSpectrum3695.graph fusedMap1937swap=true := by decide +kernel
theorem certified1937swap : Certified (graph core1937) (root 10) 2 0 :=
  of_native_maps core1937 DegreeTwoThreeSpectrum3694.graph DegreeTwoThreeSpectrum3695.graph
    sourceMap1937swap fusedMap1937swap sourceMap1937swap_checked fusedMap1937swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1937
#print axioms sourceMap1937swap_checked
#print axioms fusedMap1937swap_checked
#print axioms certified1937swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

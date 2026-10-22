/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3060 : Family 10 := level10.get ⟨1729,by decide⟩
def sourceMap3060 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3060 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3060_checked : acceptsGraphIso
    (source (graph core3060) (root 10) 0 4) DegreeTwoThreeSpectrum7358.graph sourceMap3060=true := by decide +kernel
theorem fusedMap3060_checked : acceptsGraphIso
    (fused (graph core3060) (root 10) 0 4) DegreeTwoThreeSpectrum6534.graph fusedMap3060=true := by decide +kernel
theorem certified3060 : Certified (graph core3060) (root 10) 0 4 :=
  of_native_maps core3060 DegreeTwoThreeSpectrum7358.graph DegreeTwoThreeSpectrum6534.graph
    sourceMap3060 fusedMap3060 sourceMap3060_checked fusedMap3060_checked
    DegreeTwoThreeFiniteComparisons.comparison3060
#print axioms sourceMap3060_checked
#print axioms fusedMap3060_checked
#print axioms certified3060
def sourceMap3060swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3060swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3060swap_checked : acceptsGraphIso
    (source (graph core3060) (root 10) 4 0) DegreeTwoThreeSpectrum7358.graph sourceMap3060swap=true := by decide +kernel
theorem fusedMap3060swap_checked : acceptsGraphIso
    (fused (graph core3060) (root 10) 4 0) DegreeTwoThreeSpectrum6534.graph fusedMap3060swap=true := by decide +kernel
theorem certified3060swap : Certified (graph core3060) (root 10) 4 0 :=
  of_native_maps core3060 DegreeTwoThreeSpectrum7358.graph DegreeTwoThreeSpectrum6534.graph
    sourceMap3060swap fusedMap3060swap sourceMap3060swap_checked fusedMap3060swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3060
#print axioms sourceMap3060swap_checked
#print axioms fusedMap3060swap_checked
#print axioms certified3060swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

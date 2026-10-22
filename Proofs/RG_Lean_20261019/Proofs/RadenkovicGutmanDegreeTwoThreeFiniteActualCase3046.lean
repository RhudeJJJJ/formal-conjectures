/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3046 : Family 10 := level10.get ⟨1688,by decide⟩
def sourceMap3046 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3046 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3046_checked : acceptsGraphIso
    (source (graph core3046) (root 10) 0 4) DegreeTwoThreeSpectrum7278.graph sourceMap3046=true := by decide +kernel
theorem fusedMap3046_checked : acceptsGraphIso
    (fused (graph core3046) (root 10) 0 4) DegreeTwoThreeSpectrum6356.graph fusedMap3046=true := by decide +kernel
theorem certified3046 : Certified (graph core3046) (root 10) 0 4 :=
  of_native_maps core3046 DegreeTwoThreeSpectrum7278.graph DegreeTwoThreeSpectrum6356.graph
    sourceMap3046 fusedMap3046 sourceMap3046_checked fusedMap3046_checked
    DegreeTwoThreeFiniteComparisons.comparison3046
#print axioms sourceMap3046_checked
#print axioms fusedMap3046_checked
#print axioms certified3046
def sourceMap3046swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3046swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3046swap_checked : acceptsGraphIso
    (source (graph core3046) (root 10) 4 0) DegreeTwoThreeSpectrum7278.graph sourceMap3046swap=true := by decide +kernel
theorem fusedMap3046swap_checked : acceptsGraphIso
    (fused (graph core3046) (root 10) 4 0) DegreeTwoThreeSpectrum6356.graph fusedMap3046swap=true := by decide +kernel
theorem certified3046swap : Certified (graph core3046) (root 10) 4 0 :=
  of_native_maps core3046 DegreeTwoThreeSpectrum7278.graph DegreeTwoThreeSpectrum6356.graph
    sourceMap3046swap fusedMap3046swap sourceMap3046swap_checked fusedMap3046swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3046
#print axioms sourceMap3046swap_checked
#print axioms fusedMap3046swap_checked
#print axioms certified3046swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

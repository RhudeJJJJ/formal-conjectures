/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3559 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap3559 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3559 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3559_checked : acceptsGraphIso
    (source (graph core3559) (root 8) 0 6) DegreeTwoThreeSpectrum5802.graph sourceMap3559=true := by decide +kernel
theorem fusedMap3559_checked : acceptsGraphIso
    (fused (graph core3559) (root 8) 0 6) DegreeTwoThreeSpectrum5067.graph fusedMap3559=true := by decide +kernel
theorem certified3559 : Certified (graph core3559) (root 8) 0 6 :=
  of_native_maps core3559 DegreeTwoThreeSpectrum5802.graph DegreeTwoThreeSpectrum5067.graph
    sourceMap3559 fusedMap3559 sourceMap3559_checked fusedMap3559_checked
    DegreeTwoThreeFiniteComparisons.comparison3559
#print axioms sourceMap3559_checked
#print axioms fusedMap3559_checked
#print axioms certified3559
def sourceMap3559swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3559swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3559swap_checked : acceptsGraphIso
    (source (graph core3559) (root 8) 6 0) DegreeTwoThreeSpectrum5802.graph sourceMap3559swap=true := by decide +kernel
theorem fusedMap3559swap_checked : acceptsGraphIso
    (fused (graph core3559) (root 8) 6 0) DegreeTwoThreeSpectrum5067.graph fusedMap3559swap=true := by decide +kernel
theorem certified3559swap : Certified (graph core3559) (root 8) 6 0 :=
  of_native_maps core3559 DegreeTwoThreeSpectrum5802.graph DegreeTwoThreeSpectrum5067.graph
    sourceMap3559swap fusedMap3559swap sourceMap3559swap_checked fusedMap3559swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3559
#print axioms sourceMap3559swap_checked
#print axioms fusedMap3559swap_checked
#print axioms certified3559swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

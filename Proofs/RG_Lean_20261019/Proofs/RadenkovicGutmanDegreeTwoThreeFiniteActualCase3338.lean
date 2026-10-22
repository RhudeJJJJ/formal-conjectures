/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3338 : Family 9 := level9.get ⟨340,by decide⟩
def sourceMap3338 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3338 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3338_checked : acceptsGraphIso
    (source (graph core3338) (root 9) 0 5) DegreeTwoThreeSpectrum6110.graph sourceMap3338=true := by decide +kernel
theorem fusedMap3338_checked : acceptsGraphIso
    (fused (graph core3338) (root 9) 0 5) DegreeTwoThreeSpectrum5174.graph fusedMap3338=true := by decide +kernel
theorem certified3338 : Certified (graph core3338) (root 9) 0 5 :=
  of_native_maps core3338 DegreeTwoThreeSpectrum6110.graph DegreeTwoThreeSpectrum5174.graph
    sourceMap3338 fusedMap3338 sourceMap3338_checked fusedMap3338_checked
    DegreeTwoThreeFiniteComparisons.comparison3338
#print axioms sourceMap3338_checked
#print axioms fusedMap3338_checked
#print axioms certified3338
def sourceMap3338swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3338swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3338swap_checked : acceptsGraphIso
    (source (graph core3338) (root 9) 5 0) DegreeTwoThreeSpectrum6110.graph sourceMap3338swap=true := by decide +kernel
theorem fusedMap3338swap_checked : acceptsGraphIso
    (fused (graph core3338) (root 9) 5 0) DegreeTwoThreeSpectrum5174.graph fusedMap3338swap=true := by decide +kernel
theorem certified3338swap : Certified (graph core3338) (root 9) 5 0 :=
  of_native_maps core3338 DegreeTwoThreeSpectrum6110.graph DegreeTwoThreeSpectrum5174.graph
    sourceMap3338swap fusedMap3338swap sourceMap3338swap_checked fusedMap3338swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3338
#print axioms sourceMap3338swap_checked
#print axioms fusedMap3338swap_checked
#print axioms certified3338swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

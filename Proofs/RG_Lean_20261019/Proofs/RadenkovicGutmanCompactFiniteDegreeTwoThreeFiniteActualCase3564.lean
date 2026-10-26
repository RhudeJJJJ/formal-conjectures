/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3564 : Family 8 := level8.get ⟨92,by decide⟩
def sourceMap3564 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3564 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3564_checked : acceptsGraphIso
    (source (graph core3564) (root 8) 0 6) DegreeTwoThreeSpectrum5933.graph sourceMap3564=true := by decide +kernel
theorem fusedMap3564_checked : acceptsGraphIso
    (fused (graph core3564) (root 8) 0 6) DegreeTwoThreeSpectrum5107.graph fusedMap3564=true := by decide +kernel
theorem certified3564 : Certified (graph core3564) (root 8) 0 6 :=
  of_native_maps core3564 DegreeTwoThreeSpectrum5933.graph DegreeTwoThreeSpectrum5107.graph
    sourceMap3564 fusedMap3564 sourceMap3564_checked fusedMap3564_checked
    DegreeTwoThreeFiniteComparisons.comparison3564
#print axioms sourceMap3564_checked
#print axioms fusedMap3564_checked
#print axioms certified3564
def sourceMap3564swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3564swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3564swap_checked : acceptsGraphIso
    (source (graph core3564) (root 8) 6 0) DegreeTwoThreeSpectrum5933.graph sourceMap3564swap=true := by decide +kernel
theorem fusedMap3564swap_checked : acceptsGraphIso
    (fused (graph core3564) (root 8) 6 0) DegreeTwoThreeSpectrum5107.graph fusedMap3564swap=true := by decide +kernel
theorem certified3564swap : Certified (graph core3564) (root 8) 6 0 :=
  of_native_maps core3564 DegreeTwoThreeSpectrum5933.graph DegreeTwoThreeSpectrum5107.graph
    sourceMap3564swap fusedMap3564swap sourceMap3564swap_checked fusedMap3564swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3564
#print axioms sourceMap3564swap_checked
#print axioms fusedMap3564swap_checked
#print axioms certified3564swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

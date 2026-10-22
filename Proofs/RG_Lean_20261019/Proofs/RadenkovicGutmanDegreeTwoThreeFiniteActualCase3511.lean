/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3511 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap3511 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3511 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3511_checked : acceptsGraphIso
    (source (graph core3511) (root 7) 0 6) DegreeTwoThreeSpectrum3961.graph sourceMap3511=true := by decide +kernel
theorem fusedMap3511_checked : acceptsGraphIso
    (fused (graph core3511) (root 7) 0 6) DegreeTwoThreeSpectrum3963.graph fusedMap3511=true := by decide +kernel
theorem certified3511 : Certified (graph core3511) (root 7) 0 6 :=
  of_native_maps core3511 DegreeTwoThreeSpectrum3961.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap3511 fusedMap3511 sourceMap3511_checked fusedMap3511_checked
    DegreeTwoThreeFiniteComparisons.comparison3511
#print axioms sourceMap3511_checked
#print axioms fusedMap3511_checked
#print axioms certified3511
def sourceMap3511swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3511swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3511swap_checked : acceptsGraphIso
    (source (graph core3511) (root 7) 6 0) DegreeTwoThreeSpectrum3961.graph sourceMap3511swap=true := by decide +kernel
theorem fusedMap3511swap_checked : acceptsGraphIso
    (fused (graph core3511) (root 7) 6 0) DegreeTwoThreeSpectrum3963.graph fusedMap3511swap=true := by decide +kernel
theorem certified3511swap : Certified (graph core3511) (root 7) 6 0 :=
  of_native_maps core3511 DegreeTwoThreeSpectrum3961.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap3511swap fusedMap3511swap sourceMap3511swap_checked fusedMap3511swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3511
#print axioms sourceMap3511swap_checked
#print axioms fusedMap3511swap_checked
#print axioms certified3511swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

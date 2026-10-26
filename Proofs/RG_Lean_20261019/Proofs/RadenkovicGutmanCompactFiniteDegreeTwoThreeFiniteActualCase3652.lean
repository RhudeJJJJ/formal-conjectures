/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3652 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap3652 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3652 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3652_checked : acceptsGraphIso
    (source (graph core3652) (root 6) 0 7) DegreeTwoThreeSpectrum3928.graph sourceMap3652=true := by decide +kernel
theorem fusedMap3652_checked : acceptsGraphIso
    (fused (graph core3652) (root 6) 0 7) DegreeTwoThreeSpectrum3931.graph fusedMap3652=true := by decide +kernel
theorem certified3652 : Certified (graph core3652) (root 6) 0 7 :=
  of_native_maps core3652 DegreeTwoThreeSpectrum3928.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap3652 fusedMap3652 sourceMap3652_checked fusedMap3652_checked
    DegreeTwoThreeFiniteComparisons.comparison3652
#print axioms sourceMap3652_checked
#print axioms fusedMap3652_checked
#print axioms certified3652
def sourceMap3652swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3652swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3652swap_checked : acceptsGraphIso
    (source (graph core3652) (root 6) 7 0) DegreeTwoThreeSpectrum3928.graph sourceMap3652swap=true := by decide +kernel
theorem fusedMap3652swap_checked : acceptsGraphIso
    (fused (graph core3652) (root 6) 7 0) DegreeTwoThreeSpectrum3931.graph fusedMap3652swap=true := by decide +kernel
theorem certified3652swap : Certified (graph core3652) (root 6) 7 0 :=
  of_native_maps core3652 DegreeTwoThreeSpectrum3928.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap3652swap fusedMap3652swap sourceMap3652swap_checked fusedMap3652swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3652
#print axioms sourceMap3652swap_checked
#print axioms fusedMap3652swap_checked
#print axioms certified3652swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3728 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3728 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (sourceLabel 4 0 9 v)
def fusedMap3728 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 0 9 v)
theorem sourceMap3728_checked : acceptsGraphIso
    (source (graph core3728) (root 4) 0 9) DegreeTwoThreeSpectrum3871.graph sourceMap3728=true := by decide +kernel
theorem fusedMap3728_checked : acceptsGraphIso
    (fused (graph core3728) (root 4) 0 9) DegreeTwoThreeSpectrum3876.graph fusedMap3728=true := by decide +kernel
theorem certified3728 : Certified (graph core3728) (root 4) 0 9 :=
  of_native_maps core3728 DegreeTwoThreeSpectrum3871.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap3728 fusedMap3728 sourceMap3728_checked fusedMap3728_checked
    DegreeTwoThreeFiniteComparisons.comparison3728
#print axioms sourceMap3728_checked
#print axioms fusedMap3728_checked
#print axioms certified3728
def sourceMap3728swap : (Vertices 4 ⊕ Fin 10 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,2,1,0,9,10,11,12,13,14,15,8] (sourceLabel 4 9 0 v)
def fusedMap3728swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 9 0 v)
theorem sourceMap3728swap_checked : acceptsGraphIso
    (source (graph core3728) (root 4) 9 0) DegreeTwoThreeSpectrum3871.graph sourceMap3728swap=true := by decide +kernel
theorem fusedMap3728swap_checked : acceptsGraphIso
    (fused (graph core3728) (root 4) 9 0) DegreeTwoThreeSpectrum3876.graph fusedMap3728swap=true := by decide +kernel
theorem certified3728swap : Certified (graph core3728) (root 4) 9 0 :=
  of_native_maps core3728 DegreeTwoThreeSpectrum3871.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap3728swap fusedMap3728swap sourceMap3728swap_checked fusedMap3728swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3728
#print axioms sourceMap3728swap_checked
#print axioms fusedMap3728swap_checked
#print axioms certified3728swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

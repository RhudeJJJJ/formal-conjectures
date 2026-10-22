/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3504 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap3504 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3504 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3504_checked : acceptsGraphIso
    (source (graph core3504) (root 7) 0 6) DegreeTwoThreeSpectrum4052.graph sourceMap3504=true := by decide +kernel
theorem fusedMap3504_checked : acceptsGraphIso
    (fused (graph core3504) (root 7) 0 6) DegreeTwoThreeSpectrum3866.graph fusedMap3504=true := by decide +kernel
theorem certified3504 : Certified (graph core3504) (root 7) 0 6 :=
  of_native_maps core3504 DegreeTwoThreeSpectrum4052.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap3504 fusedMap3504 sourceMap3504_checked fusedMap3504_checked
    DegreeTwoThreeFiniteComparisons.comparison3504
#print axioms sourceMap3504_checked
#print axioms fusedMap3504_checked
#print axioms certified3504
def sourceMap3504swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3504swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3504swap_checked : acceptsGraphIso
    (source (graph core3504) (root 7) 6 0) DegreeTwoThreeSpectrum4052.graph sourceMap3504swap=true := by decide +kernel
theorem fusedMap3504swap_checked : acceptsGraphIso
    (fused (graph core3504) (root 7) 6 0) DegreeTwoThreeSpectrum3866.graph fusedMap3504swap=true := by decide +kernel
theorem certified3504swap : Certified (graph core3504) (root 7) 6 0 :=
  of_native_maps core3504 DegreeTwoThreeSpectrum4052.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap3504swap fusedMap3504swap sourceMap3504swap_checked fusedMap3504swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3504
#print axioms sourceMap3504swap_checked
#print axioms fusedMap3504swap_checked
#print axioms certified3504swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

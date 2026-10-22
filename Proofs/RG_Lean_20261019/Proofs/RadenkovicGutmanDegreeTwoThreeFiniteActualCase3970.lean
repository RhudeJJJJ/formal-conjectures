/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3970 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap3970 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3970 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3970_checked : acceptsGraphIso
    (source (graph core3970) (root 7) 1 5) DegreeTwoThreeSpectrum4224.graph sourceMap3970=true := by decide +kernel
theorem fusedMap3970_checked : acceptsGraphIso
    (fused (graph core3970) (root 7) 1 5) DegreeTwoThreeSpectrum3899.graph fusedMap3970=true := by decide +kernel
theorem certified3970 : Certified (graph core3970) (root 7) 1 5 :=
  of_native_maps core3970 DegreeTwoThreeSpectrum4224.graph DegreeTwoThreeSpectrum3899.graph
    sourceMap3970 fusedMap3970 sourceMap3970_checked fusedMap3970_checked
    DegreeTwoThreeFiniteComparisons.comparison3970
#print axioms sourceMap3970_checked
#print axioms fusedMap3970_checked
#print axioms certified3970
def sourceMap3970swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3970swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3970swap_checked : acceptsGraphIso
    (source (graph core3970) (root 7) 5 1) DegreeTwoThreeSpectrum4224.graph sourceMap3970swap=true := by decide +kernel
theorem fusedMap3970swap_checked : acceptsGraphIso
    (fused (graph core3970) (root 7) 5 1) DegreeTwoThreeSpectrum3899.graph fusedMap3970swap=true := by decide +kernel
theorem certified3970swap : Certified (graph core3970) (root 7) 5 1 :=
  of_native_maps core3970 DegreeTwoThreeSpectrum4224.graph DegreeTwoThreeSpectrum3899.graph
    sourceMap3970swap fusedMap3970swap sourceMap3970swap_checked fusedMap3970swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3970
#print axioms sourceMap3970swap_checked
#print axioms fusedMap3970swap_checked
#print axioms certified3970swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

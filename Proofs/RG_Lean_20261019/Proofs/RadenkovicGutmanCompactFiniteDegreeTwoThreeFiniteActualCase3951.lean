/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3951 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap3951 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3951 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3951_checked : acceptsGraphIso
    (source (graph core3951) (root 7) 1 5) DegreeTwoThreeSpectrum3973.graph sourceMap3951=true := by decide +kernel
theorem fusedMap3951_checked : acceptsGraphIso
    (fused (graph core3951) (root 7) 1 5) DegreeTwoThreeSpectrum3858.graph fusedMap3951=true := by decide +kernel
theorem certified3951 : Certified (graph core3951) (root 7) 1 5 :=
  of_native_maps core3951 DegreeTwoThreeSpectrum3973.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap3951 fusedMap3951 sourceMap3951_checked fusedMap3951_checked
    DegreeTwoThreeFiniteComparisons.comparison3951
#print axioms sourceMap3951_checked
#print axioms fusedMap3951_checked
#print axioms certified3951
def sourceMap3951swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,15,7,8] (sourceLabel 7 5 1 v)
def fusedMap3951swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3951swap_checked : acceptsGraphIso
    (source (graph core3951) (root 7) 5 1) DegreeTwoThreeSpectrum3973.graph sourceMap3951swap=true := by decide +kernel
theorem fusedMap3951swap_checked : acceptsGraphIso
    (fused (graph core3951) (root 7) 5 1) DegreeTwoThreeSpectrum3858.graph fusedMap3951swap=true := by decide +kernel
theorem certified3951swap : Certified (graph core3951) (root 7) 5 1 :=
  of_native_maps core3951 DegreeTwoThreeSpectrum3973.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap3951swap fusedMap3951swap sourceMap3951swap_checked fusedMap3951swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3951
#print axioms sourceMap3951swap_checked
#print axioms fusedMap3951swap_checked
#print axioms certified3951swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

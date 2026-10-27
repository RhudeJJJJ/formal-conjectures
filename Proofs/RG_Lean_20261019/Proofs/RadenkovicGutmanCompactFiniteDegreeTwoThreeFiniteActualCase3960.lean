/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3960 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap3960 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3960 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3960_checked : acceptsGraphIso
    (source (graph core3960) (root 7) 1 5) DegreeTwoThreeSpectrum4435.graph sourceMap3960=true := by decide +kernel
theorem fusedMap3960_checked : acceptsGraphIso
    (fused (graph core3960) (root 7) 1 5) DegreeTwoThreeSpectrum3995.graph fusedMap3960=true := by decide +kernel
theorem certified3960 : Certified (graph core3960) (root 7) 1 5 :=
  of_native_maps core3960 DegreeTwoThreeSpectrum4435.graph DegreeTwoThreeSpectrum3995.graph
    sourceMap3960 fusedMap3960 sourceMap3960_checked fusedMap3960_checked
    DegreeTwoThreeFiniteComparisons.comparison3960
#print axioms sourceMap3960_checked
#print axioms fusedMap3960_checked
#print axioms certified3960
def sourceMap3960swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3960swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3960swap_checked : acceptsGraphIso
    (source (graph core3960) (root 7) 5 1) DegreeTwoThreeSpectrum4435.graph sourceMap3960swap=true := by decide +kernel
theorem fusedMap3960swap_checked : acceptsGraphIso
    (fused (graph core3960) (root 7) 5 1) DegreeTwoThreeSpectrum3995.graph fusedMap3960swap=true := by decide +kernel
theorem certified3960swap : Certified (graph core3960) (root 7) 5 1 :=
  of_native_maps core3960 DegreeTwoThreeSpectrum4435.graph DegreeTwoThreeSpectrum3995.graph
    sourceMap3960swap fusedMap3960swap sourceMap3960swap_checked fusedMap3960swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3960
#print axioms sourceMap3960swap_checked
#print axioms fusedMap3960swap_checked
#print axioms certified3960swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

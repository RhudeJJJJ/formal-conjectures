/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3971 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap3971 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3971 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3971_checked : acceptsGraphIso
    (source (graph core3971) (root 7) 1 5) DegreeTwoThreeSpectrum4240.graph sourceMap3971=true := by decide +kernel
theorem fusedMap3971_checked : acceptsGraphIso
    (fused (graph core3971) (root 7) 1 5) DegreeTwoThreeSpectrum3903.graph fusedMap3971=true := by decide +kernel
theorem certified3971 : Certified (graph core3971) (root 7) 1 5 :=
  of_native_maps core3971 DegreeTwoThreeSpectrum4240.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap3971 fusedMap3971 sourceMap3971_checked fusedMap3971_checked
    DegreeTwoThreeFiniteComparisons.comparison3971
#print axioms sourceMap3971_checked
#print axioms fusedMap3971_checked
#print axioms certified3971
def sourceMap3971swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3971swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3971swap_checked : acceptsGraphIso
    (source (graph core3971) (root 7) 5 1) DegreeTwoThreeSpectrum4240.graph sourceMap3971swap=true := by decide +kernel
theorem fusedMap3971swap_checked : acceptsGraphIso
    (fused (graph core3971) (root 7) 5 1) DegreeTwoThreeSpectrum3903.graph fusedMap3971swap=true := by decide +kernel
theorem certified3971swap : Certified (graph core3971) (root 7) 5 1 :=
  of_native_maps core3971 DegreeTwoThreeSpectrum4240.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap3971swap fusedMap3971swap sourceMap3971swap_checked fusedMap3971swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3971
#print axioms sourceMap3971swap_checked
#print axioms fusedMap3971swap_checked
#print axioms certified3971swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3122 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap3122 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3122 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3122_checked : acceptsGraphIso
    (source (graph core3122) (root 7) 0 5) DegreeTwoThreeSpectrum2446.graph sourceMap3122=true := by decide +kernel
theorem fusedMap3122_checked : acceptsGraphIso
    (fused (graph core3122) (root 7) 0 5) DegreeTwoThreeSpectrum2448.graph fusedMap3122=true := by decide +kernel
theorem certified3122 : Certified (graph core3122) (root 7) 0 5 :=
  of_native_maps core3122 DegreeTwoThreeSpectrum2446.graph DegreeTwoThreeSpectrum2448.graph
    sourceMap3122 fusedMap3122 sourceMap3122_checked fusedMap3122_checked
    DegreeTwoThreeFiniteComparisons.comparison3122
#print axioms sourceMap3122_checked
#print axioms fusedMap3122_checked
#print axioms certified3122
def sourceMap3122swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3122swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3122swap_checked : acceptsGraphIso
    (source (graph core3122) (root 7) 5 0) DegreeTwoThreeSpectrum2446.graph sourceMap3122swap=true := by decide +kernel
theorem fusedMap3122swap_checked : acceptsGraphIso
    (fused (graph core3122) (root 7) 5 0) DegreeTwoThreeSpectrum2448.graph fusedMap3122swap=true := by decide +kernel
theorem certified3122swap : Certified (graph core3122) (root 7) 5 0 :=
  of_native_maps core3122 DegreeTwoThreeSpectrum2446.graph DegreeTwoThreeSpectrum2448.graph
    sourceMap3122swap fusedMap3122swap sourceMap3122swap_checked fusedMap3122swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3122
#print axioms sourceMap3122swap_checked
#print axioms fusedMap3122swap_checked
#print axioms certified3122swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

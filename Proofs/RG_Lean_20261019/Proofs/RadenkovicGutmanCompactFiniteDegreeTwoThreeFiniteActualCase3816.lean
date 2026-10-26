/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3816 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap3816 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3816 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3816_checked : acceptsGraphIso
    (source (graph core3816) (root 7) 1 4) DegreeTwoThreeSpectrum3306.graph sourceMap3816=true := by decide +kernel
theorem fusedMap3816_checked : acceptsGraphIso
    (fused (graph core3816) (root 7) 1 4) DegreeTwoThreeSpectrum2569.graph fusedMap3816=true := by decide +kernel
theorem certified3816 : Certified (graph core3816) (root 7) 1 4 :=
  of_native_maps core3816 DegreeTwoThreeSpectrum3306.graph DegreeTwoThreeSpectrum2569.graph
    sourceMap3816 fusedMap3816 sourceMap3816_checked fusedMap3816_checked
    DegreeTwoThreeFiniteComparisons.comparison3816
#print axioms sourceMap3816_checked
#print axioms fusedMap3816_checked
#print axioms certified3816
def sourceMap3816swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3816swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3816swap_checked : acceptsGraphIso
    (source (graph core3816) (root 7) 4 1) DegreeTwoThreeSpectrum3306.graph sourceMap3816swap=true := by decide +kernel
theorem fusedMap3816swap_checked : acceptsGraphIso
    (fused (graph core3816) (root 7) 4 1) DegreeTwoThreeSpectrum2569.graph fusedMap3816swap=true := by decide +kernel
theorem certified3816swap : Certified (graph core3816) (root 7) 4 1 :=
  of_native_maps core3816 DegreeTwoThreeSpectrum3306.graph DegreeTwoThreeSpectrum2569.graph
    sourceMap3816swap fusedMap3816swap sourceMap3816swap_checked fusedMap3816swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3816
#print axioms sourceMap3816swap_checked
#print axioms fusedMap3816swap_checked
#print axioms certified3816swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3996 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3996 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13,14] (sourceLabel 5 1 6 v)
def fusedMap3996 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 1 6 v)
theorem sourceMap3996_checked : acceptsGraphIso
    (source (graph core3996) (root 5) 1 6) DegreeTwoThreeSpectrum2456.graph sourceMap3996=true := by decide +kernel
theorem fusedMap3996_checked : acceptsGraphIso
    (fused (graph core3996) (root 5) 1 6) DegreeTwoThreeSpectrum2315.graph fusedMap3996=true := by decide +kernel
theorem certified3996 : Certified (graph core3996) (root 5) 1 6 :=
  of_native_maps core3996 DegreeTwoThreeSpectrum2456.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap3996 fusedMap3996 sourceMap3996_checked fusedMap3996_checked
    DegreeTwoThreeFiniteComparisons.comparison3996
#print axioms sourceMap3996_checked
#print axioms fusedMap3996_checked
#print axioms certified3996
def sourceMap3996swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,14,7,8] (sourceLabel 5 6 1 v)
def fusedMap3996swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 6 1 v)
theorem sourceMap3996swap_checked : acceptsGraphIso
    (source (graph core3996) (root 5) 6 1) DegreeTwoThreeSpectrum2456.graph sourceMap3996swap=true := by decide +kernel
theorem fusedMap3996swap_checked : acceptsGraphIso
    (fused (graph core3996) (root 5) 6 1) DegreeTwoThreeSpectrum2315.graph fusedMap3996swap=true := by decide +kernel
theorem certified3996swap : Certified (graph core3996) (root 5) 6 1 :=
  of_native_maps core3996 DegreeTwoThreeSpectrum2456.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap3996swap fusedMap3996swap sourceMap3996swap_checked fusedMap3996swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3996
#print axioms sourceMap3996swap_checked
#print axioms fusedMap3996swap_checked
#print axioms certified3996swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

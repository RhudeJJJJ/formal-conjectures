/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3795 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap3795 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,6,7,8,9,10] (sourceLabel 7 1 4 v)
def fusedMap3795 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3795_checked : acceptsGraphIso
    (source (graph core3795) (root 7) 1 4) DegreeTwoThreeSpectrum2996.graph sourceMap3795=true := by decide +kernel
theorem fusedMap3795_checked : acceptsGraphIso
    (fused (graph core3795) (root 7) 1 4) DegreeTwoThreeSpectrum2431.graph fusedMap3795=true := by decide +kernel
theorem certified3795 : Certified (graph core3795) (root 7) 1 4 :=
  of_native_maps core3795 DegreeTwoThreeSpectrum2996.graph DegreeTwoThreeSpectrum2431.graph
    sourceMap3795 fusedMap3795 sourceMap3795_checked fusedMap3795_checked
    DegreeTwoThreeFiniteComparisons.comparison3795
#print axioms sourceMap3795_checked
#print axioms fusedMap3795_checked
#print axioms certified3795
def sourceMap3795swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,11,12,6,7,8,9,10,13,14] (sourceLabel 7 4 1 v)
def fusedMap3795swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3795swap_checked : acceptsGraphIso
    (source (graph core3795) (root 7) 4 1) DegreeTwoThreeSpectrum2996.graph sourceMap3795swap=true := by decide +kernel
theorem fusedMap3795swap_checked : acceptsGraphIso
    (fused (graph core3795) (root 7) 4 1) DegreeTwoThreeSpectrum2431.graph fusedMap3795swap=true := by decide +kernel
theorem certified3795swap : Certified (graph core3795) (root 7) 4 1 :=
  of_native_maps core3795 DegreeTwoThreeSpectrum2996.graph DegreeTwoThreeSpectrum2431.graph
    sourceMap3795swap fusedMap3795swap sourceMap3795swap_checked fusedMap3795swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3795
#print axioms sourceMap3795swap_checked
#print axioms fusedMap3795swap_checked
#print axioms certified3795swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

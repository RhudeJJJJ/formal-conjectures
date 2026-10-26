/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3810 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap3810 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3810 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3810_checked : acceptsGraphIso
    (source (graph core3810) (root 7) 1 4) DegreeTwoThreeSpectrum3098.graph sourceMap3810=true := by decide +kernel
theorem fusedMap3810_checked : acceptsGraphIso
    (fused (graph core3810) (root 7) 1 4) DegreeTwoThreeSpectrum2466.graph fusedMap3810=true := by decide +kernel
theorem certified3810 : Certified (graph core3810) (root 7) 1 4 :=
  of_native_maps core3810 DegreeTwoThreeSpectrum3098.graph DegreeTwoThreeSpectrum2466.graph
    sourceMap3810 fusedMap3810 sourceMap3810_checked fusedMap3810_checked
    DegreeTwoThreeFiniteComparisons.comparison3810
#print axioms sourceMap3810_checked
#print axioms fusedMap3810_checked
#print axioms certified3810
def sourceMap3810swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3810swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3810swap_checked : acceptsGraphIso
    (source (graph core3810) (root 7) 4 1) DegreeTwoThreeSpectrum3098.graph sourceMap3810swap=true := by decide +kernel
theorem fusedMap3810swap_checked : acceptsGraphIso
    (fused (graph core3810) (root 7) 4 1) DegreeTwoThreeSpectrum2466.graph fusedMap3810swap=true := by decide +kernel
theorem certified3810swap : Certified (graph core3810) (root 7) 4 1 :=
  of_native_maps core3810 DegreeTwoThreeSpectrum3098.graph DegreeTwoThreeSpectrum2466.graph
    sourceMap3810swap fusedMap3810swap sourceMap3810swap_checked fusedMap3810swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3810
#print axioms sourceMap3810swap_checked
#print axioms fusedMap3810swap_checked
#print axioms certified3810swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

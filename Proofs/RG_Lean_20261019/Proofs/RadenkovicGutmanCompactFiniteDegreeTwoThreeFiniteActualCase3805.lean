/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3805 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap3805 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3805 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3805_checked : acceptsGraphIso
    (source (graph core3805) (root 7) 1 4) DegreeTwoThreeSpectrum2881.graph sourceMap3805=true := by decide +kernel
theorem fusedMap3805_checked : acceptsGraphIso
    (fused (graph core3805) (root 7) 1 4) DegreeTwoThreeSpectrum2388.graph fusedMap3805=true := by decide +kernel
theorem certified3805 : Certified (graph core3805) (root 7) 1 4 :=
  of_native_maps core3805 DegreeTwoThreeSpectrum2881.graph DegreeTwoThreeSpectrum2388.graph
    sourceMap3805 fusedMap3805 sourceMap3805_checked fusedMap3805_checked
    DegreeTwoThreeFiniteComparisons.comparison3805
#print axioms sourceMap3805_checked
#print axioms fusedMap3805_checked
#print axioms certified3805
def sourceMap3805swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3805swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3805swap_checked : acceptsGraphIso
    (source (graph core3805) (root 7) 4 1) DegreeTwoThreeSpectrum2881.graph sourceMap3805swap=true := by decide +kernel
theorem fusedMap3805swap_checked : acceptsGraphIso
    (fused (graph core3805) (root 7) 4 1) DegreeTwoThreeSpectrum2388.graph fusedMap3805swap=true := by decide +kernel
theorem certified3805swap : Certified (graph core3805) (root 7) 4 1 :=
  of_native_maps core3805 DegreeTwoThreeSpectrum2881.graph DegreeTwoThreeSpectrum2388.graph
    sourceMap3805swap fusedMap3805swap sourceMap3805swap_checked fusedMap3805swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3805
#print axioms sourceMap3805swap_checked
#print axioms fusedMap3805swap_checked
#print axioms certified3805swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

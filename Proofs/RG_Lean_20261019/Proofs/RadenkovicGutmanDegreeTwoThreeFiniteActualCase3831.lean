/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3831 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap3831 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3831 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3831_checked : acceptsGraphIso
    (source (graph core3831) (root 8) 1 4) DegreeTwoThreeSpectrum4146.graph sourceMap3831=true := by decide +kernel
theorem fusedMap3831_checked : acceptsGraphIso
    (fused (graph core3831) (root 8) 1 4) DegreeTwoThreeSpectrum3880.graph fusedMap3831=true := by decide +kernel
theorem certified3831 : Certified (graph core3831) (root 8) 1 4 :=
  of_native_maps core3831 DegreeTwoThreeSpectrum4146.graph DegreeTwoThreeSpectrum3880.graph
    sourceMap3831 fusedMap3831 sourceMap3831_checked fusedMap3831_checked
    DegreeTwoThreeFiniteComparisons.comparison3831
#print axioms sourceMap3831_checked
#print axioms fusedMap3831_checked
#print axioms certified3831
def sourceMap3831swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3831swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3831swap_checked : acceptsGraphIso
    (source (graph core3831) (root 8) 4 1) DegreeTwoThreeSpectrum4146.graph sourceMap3831swap=true := by decide +kernel
theorem fusedMap3831swap_checked : acceptsGraphIso
    (fused (graph core3831) (root 8) 4 1) DegreeTwoThreeSpectrum3880.graph fusedMap3831swap=true := by decide +kernel
theorem certified3831swap : Certified (graph core3831) (root 8) 4 1 :=
  of_native_maps core3831 DegreeTwoThreeSpectrum4146.graph DegreeTwoThreeSpectrum3880.graph
    sourceMap3831swap fusedMap3831swap sourceMap3831swap_checked fusedMap3831swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3831
#print axioms sourceMap3831swap_checked
#print axioms fusedMap3831swap_checked
#print axioms certified3831swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

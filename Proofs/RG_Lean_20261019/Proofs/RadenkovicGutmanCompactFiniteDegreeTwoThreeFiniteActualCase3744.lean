/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3744 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3744 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 13) → Fin 17 :=
  fun v => ![6,7,8,9,5,4,3,2,1,0,10,11,12,13,14,15,16] (sourceLabel 2 0 12 v)
def fusedMap3744 : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 0 12 v)
theorem sourceMap3744_checked : acceptsGraphIso
    (source (graph core3744) (root 2) 0 12) DegreeTwoThreeSpectrum4972.graph sourceMap3744=true := by decide +kernel
theorem fusedMap3744_checked : acceptsGraphIso
    (fused (graph core3744) (root 2) 0 12) DegreeTwoThreeSpectrum4959.graph fusedMap3744=true := by decide +kernel
theorem certified3744 : Certified (graph core3744) (root 2) 0 12 :=
  of_native_maps core3744 DegreeTwoThreeSpectrum4972.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap3744 fusedMap3744 sourceMap3744_checked fusedMap3744_checked
    DegreeTwoThreeFiniteComparisons.comparison3744
#print axioms sourceMap3744_checked
#print axioms fusedMap3744_checked
#print axioms certified3744
def sourceMap3744swap : (Vertices 2 ⊕ Fin 13 ⊕ Fin 1) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 2 12 0 v)
def fusedMap3744swap : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 12 0 v)
theorem sourceMap3744swap_checked : acceptsGraphIso
    (source (graph core3744) (root 2) 12 0) DegreeTwoThreeSpectrum4972.graph sourceMap3744swap=true := by decide +kernel
theorem fusedMap3744swap_checked : acceptsGraphIso
    (fused (graph core3744) (root 2) 12 0) DegreeTwoThreeSpectrum4959.graph fusedMap3744swap=true := by decide +kernel
theorem certified3744swap : Certified (graph core3744) (root 2) 12 0 :=
  of_native_maps core3744 DegreeTwoThreeSpectrum4972.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap3744swap fusedMap3744swap sourceMap3744swap_checked fusedMap3744swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3744
#print axioms sourceMap3744swap_checked
#print axioms fusedMap3744swap_checked
#print axioms certified3744swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

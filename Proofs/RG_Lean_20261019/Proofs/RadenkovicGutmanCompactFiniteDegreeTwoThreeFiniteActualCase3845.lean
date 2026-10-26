/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3845 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap3845 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3845 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3845_checked : acceptsGraphIso
    (source (graph core3845) (root 8) 1 4) DegreeTwoThreeSpectrum4606.graph sourceMap3845=true := by decide +kernel
theorem fusedMap3845_checked : acceptsGraphIso
    (fused (graph core3845) (root 8) 1 4) DegreeTwoThreeSpectrum4089.graph fusedMap3845=true := by decide +kernel
theorem certified3845 : Certified (graph core3845) (root 8) 1 4 :=
  of_native_maps core3845 DegreeTwoThreeSpectrum4606.graph DegreeTwoThreeSpectrum4089.graph
    sourceMap3845 fusedMap3845 sourceMap3845_checked fusedMap3845_checked
    DegreeTwoThreeFiniteComparisons.comparison3845
#print axioms sourceMap3845_checked
#print axioms fusedMap3845_checked
#print axioms certified3845
def sourceMap3845swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3845swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3845swap_checked : acceptsGraphIso
    (source (graph core3845) (root 8) 4 1) DegreeTwoThreeSpectrum4606.graph sourceMap3845swap=true := by decide +kernel
theorem fusedMap3845swap_checked : acceptsGraphIso
    (fused (graph core3845) (root 8) 4 1) DegreeTwoThreeSpectrum4089.graph fusedMap3845swap=true := by decide +kernel
theorem certified3845swap : Certified (graph core3845) (root 8) 4 1 :=
  of_native_maps core3845 DegreeTwoThreeSpectrum4606.graph DegreeTwoThreeSpectrum4089.graph
    sourceMap3845swap fusedMap3845swap sourceMap3845swap_checked fusedMap3845swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3845
#print axioms sourceMap3845swap_checked
#print axioms fusedMap3845swap_checked
#print axioms certified3845swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

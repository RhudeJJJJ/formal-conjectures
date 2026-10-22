/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3440 : Family 9 := level9.get ⟨591,by decide⟩
def sourceMap3440 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3440 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3440_checked : acceptsGraphIso
    (source (graph core3440) (root 9) 0 5) DegreeTwoThreeSpectrum6192.graph sourceMap3440=true := by decide +kernel
theorem fusedMap3440_checked : acceptsGraphIso
    (fused (graph core3440) (root 9) 0 5) DegreeTwoThreeSpectrum6193.graph fusedMap3440=true := by decide +kernel
theorem certified3440 : Certified (graph core3440) (root 9) 0 5 :=
  of_native_maps core3440 DegreeTwoThreeSpectrum6192.graph DegreeTwoThreeSpectrum6193.graph
    sourceMap3440 fusedMap3440 sourceMap3440_checked fusedMap3440_checked
    DegreeTwoThreeFiniteComparisons.comparison3440
#print axioms sourceMap3440_checked
#print axioms fusedMap3440_checked
#print axioms certified3440
def sourceMap3440swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3440swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3440swap_checked : acceptsGraphIso
    (source (graph core3440) (root 9) 5 0) DegreeTwoThreeSpectrum6192.graph sourceMap3440swap=true := by decide +kernel
theorem fusedMap3440swap_checked : acceptsGraphIso
    (fused (graph core3440) (root 9) 5 0) DegreeTwoThreeSpectrum6193.graph fusedMap3440swap=true := by decide +kernel
theorem certified3440swap : Certified (graph core3440) (root 9) 5 0 :=
  of_native_maps core3440 DegreeTwoThreeSpectrum6192.graph DegreeTwoThreeSpectrum6193.graph
    sourceMap3440swap fusedMap3440swap sourceMap3440swap_checked fusedMap3440swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3440
#print axioms sourceMap3440swap_checked
#print axioms fusedMap3440swap_checked
#print axioms certified3440swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

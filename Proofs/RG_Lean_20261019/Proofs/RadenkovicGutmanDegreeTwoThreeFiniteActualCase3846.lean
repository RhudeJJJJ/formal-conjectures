/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3846 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap3846 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3846 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3846_checked : acceptsGraphIso
    (source (graph core3846) (root 8) 1 4) DegreeTwoThreeSpectrum4622.graph sourceMap3846=true := by decide +kernel
theorem fusedMap3846_checked : acceptsGraphIso
    (fused (graph core3846) (root 8) 1 4) DegreeTwoThreeSpectrum4101.graph fusedMap3846=true := by decide +kernel
theorem certified3846 : Certified (graph core3846) (root 8) 1 4 :=
  of_native_maps core3846 DegreeTwoThreeSpectrum4622.graph DegreeTwoThreeSpectrum4101.graph
    sourceMap3846 fusedMap3846 sourceMap3846_checked fusedMap3846_checked
    DegreeTwoThreeFiniteComparisons.comparison3846
#print axioms sourceMap3846_checked
#print axioms fusedMap3846_checked
#print axioms certified3846
def sourceMap3846swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3846swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3846swap_checked : acceptsGraphIso
    (source (graph core3846) (root 8) 4 1) DegreeTwoThreeSpectrum4622.graph sourceMap3846swap=true := by decide +kernel
theorem fusedMap3846swap_checked : acceptsGraphIso
    (fused (graph core3846) (root 8) 4 1) DegreeTwoThreeSpectrum4101.graph fusedMap3846swap=true := by decide +kernel
theorem certified3846swap : Certified (graph core3846) (root 8) 4 1 :=
  of_native_maps core3846 DegreeTwoThreeSpectrum4622.graph DegreeTwoThreeSpectrum4101.graph
    sourceMap3846swap fusedMap3846swap sourceMap3846swap_checked fusedMap3846swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3846
#print axioms sourceMap3846swap_checked
#print axioms fusedMap3846swap_checked
#print axioms certified3846swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

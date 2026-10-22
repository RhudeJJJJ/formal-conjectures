/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3827 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap3827 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,9,7,8,2,3,4,5,6] (sourceLabel 8 1 4 v)
def fusedMap3827 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (fusedLabel 8 1 4 v)
theorem sourceMap3827_checked : acceptsGraphIso
    (source (graph core3827) (root 8) 1 4) DegreeTwoThreeSpectrum4160.graph sourceMap3827=true := by decide +kernel
theorem fusedMap3827_checked : acceptsGraphIso
    (fused (graph core3827) (root 8) 1 4) DegreeTwoThreeSpectrum3892.graph fusedMap3827=true := by decide +kernel
theorem certified3827 : Certified (graph core3827) (root 8) 1 4 :=
  of_native_maps core3827 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3892.graph
    sourceMap3827 fusedMap3827 sourceMap3827_checked fusedMap3827_checked
    DegreeTwoThreeFiniteComparisons.comparison3827
#print axioms sourceMap3827_checked
#print axioms fusedMap3827_checked
#print axioms certified3827
def sourceMap3827swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,9,2,3,4,5,6,7,8] (sourceLabel 8 4 1 v)
def fusedMap3827swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (fusedLabel 8 4 1 v)
theorem sourceMap3827swap_checked : acceptsGraphIso
    (source (graph core3827) (root 8) 4 1) DegreeTwoThreeSpectrum4160.graph sourceMap3827swap=true := by decide +kernel
theorem fusedMap3827swap_checked : acceptsGraphIso
    (fused (graph core3827) (root 8) 4 1) DegreeTwoThreeSpectrum3892.graph fusedMap3827swap=true := by decide +kernel
theorem certified3827swap : Certified (graph core3827) (root 8) 4 1 :=
  of_native_maps core3827 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3892.graph
    sourceMap3827swap fusedMap3827swap sourceMap3827swap_checked fusedMap3827swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3827
#print axioms sourceMap3827swap_checked
#print axioms fusedMap3827swap_checked
#print axioms certified3827swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

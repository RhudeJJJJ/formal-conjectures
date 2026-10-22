/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3218 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap3218 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3218 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3218_checked : acceptsGraphIso
    (source (graph core3218) (root 8) 0 5) DegreeTwoThreeSpectrum4333.graph sourceMap3218=true := by decide +kernel
theorem fusedMap3218_checked : acceptsGraphIso
    (fused (graph core3218) (root 8) 0 5) DegreeTwoThreeSpectrum4334.graph fusedMap3218=true := by decide +kernel
theorem certified3218 : Certified (graph core3218) (root 8) 0 5 :=
  of_native_maps core3218 DegreeTwoThreeSpectrum4333.graph DegreeTwoThreeSpectrum4334.graph
    sourceMap3218 fusedMap3218 sourceMap3218_checked fusedMap3218_checked
    DegreeTwoThreeFiniteComparisons.comparison3218
#print axioms sourceMap3218_checked
#print axioms fusedMap3218_checked
#print axioms certified3218
def sourceMap3218swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3218swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3218swap_checked : acceptsGraphIso
    (source (graph core3218) (root 8) 5 0) DegreeTwoThreeSpectrum4333.graph sourceMap3218swap=true := by decide +kernel
theorem fusedMap3218swap_checked : acceptsGraphIso
    (fused (graph core3218) (root 8) 5 0) DegreeTwoThreeSpectrum4334.graph fusedMap3218swap=true := by decide +kernel
theorem certified3218swap : Certified (graph core3218) (root 8) 5 0 :=
  of_native_maps core3218 DegreeTwoThreeSpectrum4333.graph DegreeTwoThreeSpectrum4334.graph
    sourceMap3218swap fusedMap3218swap sourceMap3218swap_checked fusedMap3218swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3218
#print axioms sourceMap3218swap_checked
#print axioms fusedMap3218swap_checked
#print axioms certified3218swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

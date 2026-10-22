/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3345 : Family 9 := level9.get ⟨360,by decide⟩
def sourceMap3345 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3345 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3345_checked : acceptsGraphIso
    (source (graph core3345) (root 9) 0 5) DegreeTwoThreeSpectrum6211.graph sourceMap3345=true := by decide +kernel
theorem fusedMap3345_checked : acceptsGraphIso
    (fused (graph core3345) (root 9) 0 5) DegreeTwoThreeSpectrum5230.graph fusedMap3345=true := by decide +kernel
theorem certified3345 : Certified (graph core3345) (root 9) 0 5 :=
  of_native_maps core3345 DegreeTwoThreeSpectrum6211.graph DegreeTwoThreeSpectrum5230.graph
    sourceMap3345 fusedMap3345 sourceMap3345_checked fusedMap3345_checked
    DegreeTwoThreeFiniteComparisons.comparison3345
#print axioms sourceMap3345_checked
#print axioms fusedMap3345_checked
#print axioms certified3345
def sourceMap3345swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3345swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3345swap_checked : acceptsGraphIso
    (source (graph core3345) (root 9) 5 0) DegreeTwoThreeSpectrum6211.graph sourceMap3345swap=true := by decide +kernel
theorem fusedMap3345swap_checked : acceptsGraphIso
    (fused (graph core3345) (root 9) 5 0) DegreeTwoThreeSpectrum5230.graph fusedMap3345swap=true := by decide +kernel
theorem certified3345swap : Certified (graph core3345) (root 9) 5 0 :=
  of_native_maps core3345 DegreeTwoThreeSpectrum6211.graph DegreeTwoThreeSpectrum5230.graph
    sourceMap3345swap fusedMap3345swap sourceMap3345swap_checked fusedMap3345swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3345
#print axioms sourceMap3345swap_checked
#print axioms fusedMap3345swap_checked
#print axioms certified3345swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

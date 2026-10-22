/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3319 : Family 9 := level9.get ⟨291,by decide⟩
def sourceMap3319 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3319 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3319_checked : acceptsGraphIso
    (source (graph core3319) (root 9) 0 5) DegreeTwoThreeSpectrum5835.graph sourceMap3319=true := by decide +kernel
theorem fusedMap3319_checked : acceptsGraphIso
    (fused (graph core3319) (root 9) 0 5) DegreeTwoThreeSpectrum5836.graph fusedMap3319=true := by decide +kernel
theorem certified3319 : Certified (graph core3319) (root 9) 0 5 :=
  of_native_maps core3319 DegreeTwoThreeSpectrum5835.graph DegreeTwoThreeSpectrum5836.graph
    sourceMap3319 fusedMap3319 sourceMap3319_checked fusedMap3319_checked
    DegreeTwoThreeFiniteComparisons.comparison3319
#print axioms sourceMap3319_checked
#print axioms fusedMap3319_checked
#print axioms certified3319
def sourceMap3319swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3319swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3319swap_checked : acceptsGraphIso
    (source (graph core3319) (root 9) 5 0) DegreeTwoThreeSpectrum5835.graph sourceMap3319swap=true := by decide +kernel
theorem fusedMap3319swap_checked : acceptsGraphIso
    (fused (graph core3319) (root 9) 5 0) DegreeTwoThreeSpectrum5836.graph fusedMap3319swap=true := by decide +kernel
theorem certified3319swap : Certified (graph core3319) (root 9) 5 0 :=
  of_native_maps core3319 DegreeTwoThreeSpectrum5835.graph DegreeTwoThreeSpectrum5836.graph
    sourceMap3319swap fusedMap3319swap sourceMap3319swap_checked fusedMap3319swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3319
#print axioms sourceMap3319swap_checked
#print axioms fusedMap3319swap_checked
#print axioms certified3319swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

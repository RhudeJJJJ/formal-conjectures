/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5319 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5319 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,10,7,8,9,2,1,0,11,12,13,14,15,16] (sourceLabel 4 2 8 v)
def fusedMap5319 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 2 8 v)
theorem sourceMap5319_checked : acceptsGraphIso
    (source (graph core5319) (root 4) 2 8) DegreeTwoThreeSpectrum5661.graph sourceMap5319=true := by decide +kernel
theorem fusedMap5319_checked : acceptsGraphIso
    (fused (graph core5319) (root 4) 2 8) DegreeTwoThreeSpectrum4961.graph fusedMap5319=true := by decide +kernel
theorem certified5319 : Certified (graph core5319) (root 4) 2 8 :=
  of_native_maps core5319 DegreeTwoThreeSpectrum5661.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap5319 fusedMap5319 sourceMap5319_checked fusedMap5319_checked
    DegreeTwoThreeFiniteComparisons.comparison5319
#print axioms sourceMap5319_checked
#print axioms fusedMap5319_checked
#print axioms certified5319
def sourceMap5319swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,4,5,6,10,2,1,0,11,12,13,14,15,16,7,8,9] (sourceLabel 4 8 2 v)
def fusedMap5319swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 8 2 v)
theorem sourceMap5319swap_checked : acceptsGraphIso
    (source (graph core5319) (root 4) 8 2) DegreeTwoThreeSpectrum5661.graph sourceMap5319swap=true := by decide +kernel
theorem fusedMap5319swap_checked : acceptsGraphIso
    (fused (graph core5319) (root 4) 8 2) DegreeTwoThreeSpectrum4961.graph fusedMap5319swap=true := by decide +kernel
theorem certified5319swap : Certified (graph core5319) (root 4) 8 2 :=
  of_native_maps core5319 DegreeTwoThreeSpectrum5661.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap5319swap fusedMap5319swap sourceMap5319swap_checked fusedMap5319swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5319
#print axioms sourceMap5319swap_checked
#print axioms fusedMap5319swap_checked
#print axioms certified5319swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

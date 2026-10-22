/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1319 : Family 9 := level9.get ⟨403,by decide⟩
def sourceMap1319 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1319 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1319_checked : acceptsGraphIso
    (source (graph core1319) (root 9) 0 2) DegreeTwoThreeSpectrum2061.graph sourceMap1319=true := by decide +kernel
theorem fusedMap1319_checked : acceptsGraphIso
    (fused (graph core1319) (root 9) 0 2) DegreeTwoThreeSpectrum2065.graph fusedMap1319=true := by decide +kernel
theorem certified1319 : Certified (graph core1319) (root 9) 0 2 :=
  of_native_maps core1319 DegreeTwoThreeSpectrum2061.graph DegreeTwoThreeSpectrum2065.graph
    sourceMap1319 fusedMap1319 sourceMap1319_checked fusedMap1319_checked
    DegreeTwoThreeFiniteComparisons.comparison1319
#print axioms sourceMap1319_checked
#print axioms fusedMap1319_checked
#print axioms certified1319
def sourceMap1319swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1319swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1319swap_checked : acceptsGraphIso
    (source (graph core1319) (root 9) 2 0) DegreeTwoThreeSpectrum2061.graph sourceMap1319swap=true := by decide +kernel
theorem fusedMap1319swap_checked : acceptsGraphIso
    (fused (graph core1319) (root 9) 2 0) DegreeTwoThreeSpectrum2065.graph fusedMap1319swap=true := by decide +kernel
theorem certified1319swap : Certified (graph core1319) (root 9) 2 0 :=
  of_native_maps core1319 DegreeTwoThreeSpectrum2061.graph DegreeTwoThreeSpectrum2065.graph
    sourceMap1319swap fusedMap1319swap sourceMap1319swap_checked fusedMap1319swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1319
#print axioms sourceMap1319swap_checked
#print axioms fusedMap1319swap_checked
#print axioms certified1319swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

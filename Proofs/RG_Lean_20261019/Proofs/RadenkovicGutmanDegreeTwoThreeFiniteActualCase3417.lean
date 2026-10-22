/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3417 : Family 9 := level9.get ⟨530,by decide⟩
def sourceMap3417 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3417 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3417_checked : acceptsGraphIso
    (source (graph core3417) (root 9) 0 5) DegreeTwoThreeSpectrum7009.graph sourceMap3417=true := by decide +kernel
theorem fusedMap3417_checked : acceptsGraphIso
    (fused (graph core3417) (root 9) 0 5) DegreeTwoThreeSpectrum5826.graph fusedMap3417=true := by decide +kernel
theorem certified3417 : Certified (graph core3417) (root 9) 0 5 :=
  of_native_maps core3417 DegreeTwoThreeSpectrum7009.graph DegreeTwoThreeSpectrum5826.graph
    sourceMap3417 fusedMap3417 sourceMap3417_checked fusedMap3417_checked
    DegreeTwoThreeFiniteComparisons.comparison3417
#print axioms sourceMap3417_checked
#print axioms fusedMap3417_checked
#print axioms certified3417
def sourceMap3417swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3417swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3417swap_checked : acceptsGraphIso
    (source (graph core3417) (root 9) 5 0) DegreeTwoThreeSpectrum7009.graph sourceMap3417swap=true := by decide +kernel
theorem fusedMap3417swap_checked : acceptsGraphIso
    (fused (graph core3417) (root 9) 5 0) DegreeTwoThreeSpectrum5826.graph fusedMap3417swap=true := by decide +kernel
theorem certified3417swap : Certified (graph core3417) (root 9) 5 0 :=
  of_native_maps core3417 DegreeTwoThreeSpectrum7009.graph DegreeTwoThreeSpectrum5826.graph
    sourceMap3417swap fusedMap3417swap sourceMap3417swap_checked fusedMap3417swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3417
#print axioms sourceMap3417swap_checked
#print axioms fusedMap3417swap_checked
#print axioms certified3417swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

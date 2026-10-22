/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3339 : Family 9 := level9.get ⟨345,by decide⟩
def sourceMap3339 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3339 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3339_checked : acceptsGraphIso
    (source (graph core3339) (root 9) 0 5) DegreeTwoThreeSpectrum6136.graph sourceMap3339=true := by decide +kernel
theorem fusedMap3339_checked : acceptsGraphIso
    (fused (graph core3339) (root 9) 0 5) DegreeTwoThreeSpectrum5186.graph fusedMap3339=true := by decide +kernel
theorem certified3339 : Certified (graph core3339) (root 9) 0 5 :=
  of_native_maps core3339 DegreeTwoThreeSpectrum6136.graph DegreeTwoThreeSpectrum5186.graph
    sourceMap3339 fusedMap3339 sourceMap3339_checked fusedMap3339_checked
    DegreeTwoThreeFiniteComparisons.comparison3339
#print axioms sourceMap3339_checked
#print axioms fusedMap3339_checked
#print axioms certified3339
def sourceMap3339swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3339swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3339swap_checked : acceptsGraphIso
    (source (graph core3339) (root 9) 5 0) DegreeTwoThreeSpectrum6136.graph sourceMap3339swap=true := by decide +kernel
theorem fusedMap3339swap_checked : acceptsGraphIso
    (fused (graph core3339) (root 9) 5 0) DegreeTwoThreeSpectrum5186.graph fusedMap3339swap=true := by decide +kernel
theorem certified3339swap : Certified (graph core3339) (root 9) 5 0 :=
  of_native_maps core3339 DegreeTwoThreeSpectrum6136.graph DegreeTwoThreeSpectrum5186.graph
    sourceMap3339swap fusedMap3339swap sourceMap3339swap_checked fusedMap3339swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3339
#print axioms sourceMap3339swap_checked
#print axioms fusedMap3339swap_checked
#print axioms certified3339swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

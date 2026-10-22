/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3337 : Family 9 := level9.get ⟨339,by decide⟩
def sourceMap3337 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3337 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3337_checked : acceptsGraphIso
    (source (graph core3337) (root 9) 0 5) DegreeTwoThreeSpectrum6104.graph sourceMap3337=true := by decide +kernel
theorem fusedMap3337_checked : acceptsGraphIso
    (fused (graph core3337) (root 9) 0 5) DegreeTwoThreeSpectrum5171.graph fusedMap3337=true := by decide +kernel
theorem certified3337 : Certified (graph core3337) (root 9) 0 5 :=
  of_native_maps core3337 DegreeTwoThreeSpectrum6104.graph DegreeTwoThreeSpectrum5171.graph
    sourceMap3337 fusedMap3337 sourceMap3337_checked fusedMap3337_checked
    DegreeTwoThreeFiniteComparisons.comparison3337
#print axioms sourceMap3337_checked
#print axioms fusedMap3337_checked
#print axioms certified3337
def sourceMap3337swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3337swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3337swap_checked : acceptsGraphIso
    (source (graph core3337) (root 9) 5 0) DegreeTwoThreeSpectrum6104.graph sourceMap3337swap=true := by decide +kernel
theorem fusedMap3337swap_checked : acceptsGraphIso
    (fused (graph core3337) (root 9) 5 0) DegreeTwoThreeSpectrum5171.graph fusedMap3337swap=true := by decide +kernel
theorem certified3337swap : Certified (graph core3337) (root 9) 5 0 :=
  of_native_maps core3337 DegreeTwoThreeSpectrum6104.graph DegreeTwoThreeSpectrum5171.graph
    sourceMap3337swap fusedMap3337swap sourceMap3337swap_checked fusedMap3337swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3337
#print axioms sourceMap3337swap_checked
#print axioms fusedMap3337swap_checked
#print axioms certified3337swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

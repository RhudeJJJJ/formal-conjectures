/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3288 : Family 9 := level9.get ⟨196,by decide⟩
def sourceMap3288 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3288 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3288_checked : acceptsGraphIso
    (source (graph core3288) (root 9) 0 5) DegreeTwoThreeSpectrum5402.graph sourceMap3288=true := by decide +kernel
theorem fusedMap3288_checked : acceptsGraphIso
    (fused (graph core3288) (root 9) 0 5) DegreeTwoThreeSpectrum5403.graph fusedMap3288=true := by decide +kernel
theorem certified3288 : Certified (graph core3288) (root 9) 0 5 :=
  of_native_maps core3288 DegreeTwoThreeSpectrum5402.graph DegreeTwoThreeSpectrum5403.graph
    sourceMap3288 fusedMap3288 sourceMap3288_checked fusedMap3288_checked
    DegreeTwoThreeFiniteComparisons.comparison3288
#print axioms sourceMap3288_checked
#print axioms fusedMap3288_checked
#print axioms certified3288
def sourceMap3288swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3288swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3288swap_checked : acceptsGraphIso
    (source (graph core3288) (root 9) 5 0) DegreeTwoThreeSpectrum5402.graph sourceMap3288swap=true := by decide +kernel
theorem fusedMap3288swap_checked : acceptsGraphIso
    (fused (graph core3288) (root 9) 5 0) DegreeTwoThreeSpectrum5403.graph fusedMap3288swap=true := by decide +kernel
theorem certified3288swap : Certified (graph core3288) (root 9) 5 0 :=
  of_native_maps core3288 DegreeTwoThreeSpectrum5402.graph DegreeTwoThreeSpectrum5403.graph
    sourceMap3288swap fusedMap3288swap sourceMap3288swap_checked fusedMap3288swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3288
#print axioms sourceMap3288swap_checked
#print axioms fusedMap3288swap_checked
#print axioms certified3288swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

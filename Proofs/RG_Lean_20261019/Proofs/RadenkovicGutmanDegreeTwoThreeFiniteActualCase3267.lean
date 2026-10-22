/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3267 : Family 9 := level9.get ⟨131,by decide⟩
def sourceMap3267 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 9 0 5 v)
def fusedMap3267 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3267_checked : acceptsGraphIso
    (source (graph core3267) (root 9) 0 5) DegreeTwoThreeSpectrum5952.graph sourceMap3267=true := by decide +kernel
theorem fusedMap3267_checked : acceptsGraphIso
    (fused (graph core3267) (root 9) 0 5) DegreeTwoThreeSpectrum5116.graph fusedMap3267=true := by decide +kernel
theorem certified3267 : Certified (graph core3267) (root 9) 0 5 :=
  of_native_maps core3267 DegreeTwoThreeSpectrum5952.graph DegreeTwoThreeSpectrum5116.graph
    sourceMap3267 fusedMap3267 sourceMap3267_checked fusedMap3267_checked
    DegreeTwoThreeFiniteComparisons.comparison3267
#print axioms sourceMap3267_checked
#print axioms fusedMap3267_checked
#print axioms certified3267
def sourceMap3267swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13,16] (sourceLabel 9 5 0 v)
def fusedMap3267swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3267swap_checked : acceptsGraphIso
    (source (graph core3267) (root 9) 5 0) DegreeTwoThreeSpectrum5952.graph sourceMap3267swap=true := by decide +kernel
theorem fusedMap3267swap_checked : acceptsGraphIso
    (fused (graph core3267) (root 9) 5 0) DegreeTwoThreeSpectrum5116.graph fusedMap3267swap=true := by decide +kernel
theorem certified3267swap : Certified (graph core3267) (root 9) 5 0 :=
  of_native_maps core3267 DegreeTwoThreeSpectrum5952.graph DegreeTwoThreeSpectrum5116.graph
    sourceMap3267swap fusedMap3267swap sourceMap3267swap_checked fusedMap3267swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3267
#print axioms sourceMap3267swap_checked
#print axioms fusedMap3267swap_checked
#print axioms certified3267swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

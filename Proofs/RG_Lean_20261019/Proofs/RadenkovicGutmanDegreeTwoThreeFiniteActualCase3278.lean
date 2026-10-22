/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3278 : Family 9 := level9.get ⟨171,by decide⟩
def sourceMap3278 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3278 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3278_checked : acceptsGraphIso
    (source (graph core3278) (root 9) 0 5) DegreeTwoThreeSpectrum5290.graph sourceMap3278=true := by decide +kernel
theorem fusedMap3278_checked : acceptsGraphIso
    (fused (graph core3278) (root 9) 0 5) DegreeTwoThreeSpectrum5291.graph fusedMap3278=true := by decide +kernel
theorem certified3278 : Certified (graph core3278) (root 9) 0 5 :=
  of_native_maps core3278 DegreeTwoThreeSpectrum5290.graph DegreeTwoThreeSpectrum5291.graph
    sourceMap3278 fusedMap3278 sourceMap3278_checked fusedMap3278_checked
    DegreeTwoThreeFiniteComparisons.comparison3278
#print axioms sourceMap3278_checked
#print axioms fusedMap3278_checked
#print axioms certified3278
def sourceMap3278swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3278swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3278swap_checked : acceptsGraphIso
    (source (graph core3278) (root 9) 5 0) DegreeTwoThreeSpectrum5290.graph sourceMap3278swap=true := by decide +kernel
theorem fusedMap3278swap_checked : acceptsGraphIso
    (fused (graph core3278) (root 9) 5 0) DegreeTwoThreeSpectrum5291.graph fusedMap3278swap=true := by decide +kernel
theorem certified3278swap : Certified (graph core3278) (root 9) 5 0 :=
  of_native_maps core3278 DegreeTwoThreeSpectrum5290.graph DegreeTwoThreeSpectrum5291.graph
    sourceMap3278swap fusedMap3278swap sourceMap3278swap_checked fusedMap3278swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3278
#print axioms sourceMap3278swap_checked
#print axioms fusedMap3278swap_checked
#print axioms certified3278swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

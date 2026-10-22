/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3321 : Family 9 := level9.get ⟨297,by decide⟩
def sourceMap3321 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3321 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3321_checked : acceptsGraphIso
    (source (graph core3321) (root 9) 0 5) DegreeTwoThreeSpectrum5853.graph sourceMap3321=true := by decide +kernel
theorem fusedMap3321_checked : acceptsGraphIso
    (fused (graph core3321) (root 9) 0 5) DegreeTwoThreeSpectrum5854.graph fusedMap3321=true := by decide +kernel
theorem certified3321 : Certified (graph core3321) (root 9) 0 5 :=
  of_native_maps core3321 DegreeTwoThreeSpectrum5853.graph DegreeTwoThreeSpectrum5854.graph
    sourceMap3321 fusedMap3321 sourceMap3321_checked fusedMap3321_checked
    DegreeTwoThreeFiniteComparisons.comparison3321
#print axioms sourceMap3321_checked
#print axioms fusedMap3321_checked
#print axioms certified3321
def sourceMap3321swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3321swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3321swap_checked : acceptsGraphIso
    (source (graph core3321) (root 9) 5 0) DegreeTwoThreeSpectrum5853.graph sourceMap3321swap=true := by decide +kernel
theorem fusedMap3321swap_checked : acceptsGraphIso
    (fused (graph core3321) (root 9) 5 0) DegreeTwoThreeSpectrum5854.graph fusedMap3321swap=true := by decide +kernel
theorem certified3321swap : Certified (graph core3321) (root 9) 5 0 :=
  of_native_maps core3321 DegreeTwoThreeSpectrum5853.graph DegreeTwoThreeSpectrum5854.graph
    sourceMap3321swap fusedMap3321swap sourceMap3321swap_checked fusedMap3321swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3321
#print axioms sourceMap3321swap_checked
#print axioms fusedMap3321swap_checked
#print axioms certified3321swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2061 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap2061 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap2061 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap2061_checked : acceptsGraphIso
    (source (graph core2061) (root 5) 0 4) DegreeOneSmallSpectrum469.graph sourceMap2061=true := by decide +kernel
theorem fusedMap2061_checked : acceptsGraphIso
    (fused (graph core2061) (root 5) 0 4) DegreeOneSmallSpectrum372.graph fusedMap2061=true := by decide +kernel
theorem certified2061 : Certified (graph core2061) (root 5) 0 4 :=
  of_native_maps core2061 DegreeOneSmallSpectrum469.graph DegreeOneSmallSpectrum372.graph
    sourceMap2061 fusedMap2061 sourceMap2061_checked fusedMap2061_checked
    DegreeTwoThreeFiniteComparisons.comparison2061
#print axioms sourceMap2061_checked
#print axioms fusedMap2061_checked
#print axioms certified2061
def sourceMap2061swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap2061swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap2061swap_checked : acceptsGraphIso
    (source (graph core2061) (root 5) 4 0) DegreeOneSmallSpectrum469.graph sourceMap2061swap=true := by decide +kernel
theorem fusedMap2061swap_checked : acceptsGraphIso
    (fused (graph core2061) (root 5) 4 0) DegreeOneSmallSpectrum372.graph fusedMap2061swap=true := by decide +kernel
theorem certified2061swap : Certified (graph core2061) (root 5) 4 0 :=
  of_native_maps core2061 DegreeOneSmallSpectrum469.graph DegreeOneSmallSpectrum372.graph
    sourceMap2061swap fusedMap2061swap sourceMap2061swap_checked fusedMap2061swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2061
#print axioms sourceMap2061swap_checked
#print axioms fusedMap2061swap_checked
#print axioms certified2061swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

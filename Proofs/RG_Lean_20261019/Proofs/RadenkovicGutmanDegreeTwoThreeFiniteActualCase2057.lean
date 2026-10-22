/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2057 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap2057 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap2057 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap2057_checked : acceptsGraphIso
    (source (graph core2057) (root 4) 0 4) DegreeOneSmallSpectrum225.graph sourceMap2057=true := by decide +kernel
theorem fusedMap2057_checked : acceptsGraphIso
    (fused (graph core2057) (root 4) 0 4) DegreeOneSmallSpectrum166.graph fusedMap2057=true := by decide +kernel
theorem certified2057 : Certified (graph core2057) (root 4) 0 4 :=
  of_native_maps core2057 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum166.graph
    sourceMap2057 fusedMap2057 sourceMap2057_checked fusedMap2057_checked
    DegreeTwoThreeFiniteComparisons.comparison2057
#print axioms sourceMap2057_checked
#print axioms fusedMap2057_checked
#print axioms certified2057
def sourceMap2057swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap2057swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap2057swap_checked : acceptsGraphIso
    (source (graph core2057) (root 4) 4 0) DegreeOneSmallSpectrum225.graph sourceMap2057swap=true := by decide +kernel
theorem fusedMap2057swap_checked : acceptsGraphIso
    (fused (graph core2057) (root 4) 4 0) DegreeOneSmallSpectrum166.graph fusedMap2057swap=true := by decide +kernel
theorem certified2057swap : Certified (graph core2057) (root 4) 4 0 :=
  of_native_maps core2057 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum166.graph
    sourceMap2057swap fusedMap2057swap sourceMap2057swap_checked fusedMap2057swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2057
#print axioms sourceMap2057swap_checked
#print axioms fusedMap2057swap_checked
#print axioms certified2057swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

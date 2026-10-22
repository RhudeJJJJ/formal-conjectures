/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2062 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap2062 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap2062 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap2062_checked : acceptsGraphIso
    (source (graph core2062) (root 5) 0 4) DegreeOneSmallSpectrum544.graph sourceMap2062=true := by decide +kernel
theorem fusedMap2062_checked : acceptsGraphIso
    (fused (graph core2062) (root 5) 0 4) DegreeOneSmallSpectrum381.graph fusedMap2062=true := by decide +kernel
theorem certified2062 : Certified (graph core2062) (root 5) 0 4 :=
  of_native_maps core2062 DegreeOneSmallSpectrum544.graph DegreeOneSmallSpectrum381.graph
    sourceMap2062 fusedMap2062 sourceMap2062_checked fusedMap2062_checked
    DegreeTwoThreeFiniteComparisons.comparison2062
#print axioms sourceMap2062_checked
#print axioms fusedMap2062_checked
#print axioms certified2062
def sourceMap2062swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap2062swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap2062swap_checked : acceptsGraphIso
    (source (graph core2062) (root 5) 4 0) DegreeOneSmallSpectrum544.graph sourceMap2062swap=true := by decide +kernel
theorem fusedMap2062swap_checked : acceptsGraphIso
    (fused (graph core2062) (root 5) 4 0) DegreeOneSmallSpectrum381.graph fusedMap2062swap=true := by decide +kernel
theorem certified2062swap : Certified (graph core2062) (root 5) 4 0 :=
  of_native_maps core2062 DegreeOneSmallSpectrum544.graph DegreeOneSmallSpectrum381.graph
    sourceMap2062swap fusedMap2062swap sourceMap2062swap_checked fusedMap2062swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2062
#print axioms sourceMap2062swap_checked
#print axioms fusedMap2062swap_checked
#print axioms certified2062swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

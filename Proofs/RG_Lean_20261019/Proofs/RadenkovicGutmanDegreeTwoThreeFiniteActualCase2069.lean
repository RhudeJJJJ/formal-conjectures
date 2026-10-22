/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2069 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap2069 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2069 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2069_checked : acceptsGraphIso
    (source (graph core2069) (root 6) 0 4) DegreeOneSmallSpectrum958.graph sourceMap2069=true := by decide +kernel
theorem fusedMap2069_checked : acceptsGraphIso
    (fused (graph core2069) (root 6) 0 4) DegreeOneSmallSpectrum961.graph fusedMap2069=true := by decide +kernel
theorem certified2069 : Certified (graph core2069) (root 6) 0 4 :=
  of_native_maps core2069 DegreeOneSmallSpectrum958.graph DegreeOneSmallSpectrum961.graph
    sourceMap2069 fusedMap2069 sourceMap2069_checked fusedMap2069_checked
    DegreeTwoThreeFiniteComparisons.comparison2069
#print axioms sourceMap2069_checked
#print axioms fusedMap2069_checked
#print axioms certified2069
def sourceMap2069swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap2069swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2069swap_checked : acceptsGraphIso
    (source (graph core2069) (root 6) 4 0) DegreeOneSmallSpectrum958.graph sourceMap2069swap=true := by decide +kernel
theorem fusedMap2069swap_checked : acceptsGraphIso
    (fused (graph core2069) (root 6) 4 0) DegreeOneSmallSpectrum961.graph fusedMap2069swap=true := by decide +kernel
theorem certified2069swap : Certified (graph core2069) (root 6) 4 0 :=
  of_native_maps core2069 DegreeOneSmallSpectrum958.graph DegreeOneSmallSpectrum961.graph
    sourceMap2069swap fusedMap2069swap sourceMap2069swap_checked fusedMap2069swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2069
#print axioms sourceMap2069swap_checked
#print axioms fusedMap2069swap_checked
#print axioms certified2069swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1039 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap1039 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7] (sourceLabel 5 0 2 v)
def fusedMap1039 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap1039_checked : acceptsGraphIso
    (source (graph core1039) (root 5) 0 2) DegreeOneSmallSpectrum145.graph sourceMap1039=true := by decide +kernel
theorem fusedMap1039_checked : acceptsGraphIso
    (fused (graph core1039) (root 5) 0 2) DegreeOneSmallSpectrum083.graph fusedMap1039=true := by decide +kernel
theorem certified1039 : Certified (graph core1039) (root 5) 0 2 :=
  of_native_maps core1039 DegreeOneSmallSpectrum145.graph DegreeOneSmallSpectrum083.graph
    sourceMap1039 fusedMap1039 sourceMap1039_checked fusedMap1039_checked
    DegreeTwoThreeFiniteComparisons.comparison1039
#print axioms sourceMap1039_checked
#print axioms fusedMap1039_checked
#print axioms certified1039
def sourceMap1039swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,8,5,6,7,9] (sourceLabel 5 2 0 v)
def fusedMap1039swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap1039swap_checked : acceptsGraphIso
    (source (graph core1039) (root 5) 2 0) DegreeOneSmallSpectrum145.graph sourceMap1039swap=true := by decide +kernel
theorem fusedMap1039swap_checked : acceptsGraphIso
    (fused (graph core1039) (root 5) 2 0) DegreeOneSmallSpectrum083.graph fusedMap1039swap=true := by decide +kernel
theorem certified1039swap : Certified (graph core1039) (root 5) 2 0 :=
  of_native_maps core1039 DegreeOneSmallSpectrum145.graph DegreeOneSmallSpectrum083.graph
    sourceMap1039swap fusedMap1039swap sourceMap1039swap_checked fusedMap1039swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1039
#print axioms sourceMap1039swap_checked
#print axioms fusedMap1039swap_checked
#print axioms certified1039swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1036 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap1036 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 0 2 v)
def fusedMap1036 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap1036_checked : acceptsGraphIso
    (source (graph core1036) (root 4) 0 2) DegreeOneSmallSpectrum053.graph sourceMap1036=true := by decide +kernel
theorem fusedMap1036_checked : acceptsGraphIso
    (fused (graph core1036) (root 4) 0 2) DegreeOneSmallSpectrum055.graph fusedMap1036=true := by decide +kernel
theorem certified1036 : Certified (graph core1036) (root 4) 0 2 :=
  of_native_maps core1036 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum055.graph
    sourceMap1036 fusedMap1036 sourceMap1036_checked fusedMap1036_checked
    DegreeTwoThreeFiniteComparisons.comparison1036
#print axioms sourceMap1036_checked
#print axioms fusedMap1036_checked
#print axioms certified1036
def sourceMap1036swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,6,7,8,5] (sourceLabel 4 2 0 v)
def fusedMap1036swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap1036swap_checked : acceptsGraphIso
    (source (graph core1036) (root 4) 2 0) DegreeOneSmallSpectrum053.graph sourceMap1036swap=true := by decide +kernel
theorem fusedMap1036swap_checked : acceptsGraphIso
    (fused (graph core1036) (root 4) 2 0) DegreeOneSmallSpectrum055.graph fusedMap1036swap=true := by decide +kernel
theorem certified1036swap : Certified (graph core1036) (root 4) 2 0 :=
  of_native_maps core1036 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum055.graph
    sourceMap1036swap fusedMap1036swap sourceMap1036swap_checked fusedMap1036swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1036
#print axioms sourceMap1036swap_checked
#print axioms fusedMap1036swap_checked
#print axioms certified1036swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

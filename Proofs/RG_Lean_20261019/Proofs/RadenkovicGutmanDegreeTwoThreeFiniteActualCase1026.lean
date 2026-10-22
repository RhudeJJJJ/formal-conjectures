/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1026 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap1026 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,6,7,8,4,5,2,3] (sourceLabel 5 0 1 v)
def fusedMap1026 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,5,6,7,8,4,1,2,3] (fusedLabel 5 0 1 v)
theorem sourceMap1026_checked : acceptsGraphIso
    (source (graph core1026) (root 5) 0 1) DegreeOneSmallSpectrum058.graph sourceMap1026=true := by decide +kernel
theorem fusedMap1026_checked : acceptsGraphIso
    (fused (graph core1026) (root 5) 0 1) DegreeOneSmallSpectrum036.graph fusedMap1026=true := by decide +kernel
theorem certified1026 : Certified (graph core1026) (root 5) 0 1 :=
  of_native_maps core1026 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum036.graph
    sourceMap1026 fusedMap1026 sourceMap1026_checked fusedMap1026_checked
    DegreeTwoThreeFiniteComparisons.comparison1026
#print axioms sourceMap1026_checked
#print axioms fusedMap1026_checked
#print axioms certified1026
def sourceMap1026swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,4,2,3,5] (sourceLabel 5 1 0 v)
def fusedMap1026swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,5,6,7,8,4,1,2,3] (fusedLabel 5 1 0 v)
theorem sourceMap1026swap_checked : acceptsGraphIso
    (source (graph core1026) (root 5) 1 0) DegreeOneSmallSpectrum058.graph sourceMap1026swap=true := by decide +kernel
theorem fusedMap1026swap_checked : acceptsGraphIso
    (fused (graph core1026) (root 5) 1 0) DegreeOneSmallSpectrum036.graph fusedMap1026swap=true := by decide +kernel
theorem certified1026swap : Certified (graph core1026) (root 5) 1 0 :=
  of_native_maps core1026 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum036.graph
    sourceMap1026swap fusedMap1026swap sourceMap1026swap_checked fusedMap1026swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1026
#print axioms sourceMap1026swap_checked
#print axioms fusedMap1026swap_checked
#print axioms certified1026swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

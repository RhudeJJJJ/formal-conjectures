/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1037 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap1037 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,6,7,8,9,4,5,1,2,3] (sourceLabel 5 0 2 v)
def fusedMap1037 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,9,5,6,7,8] (fusedLabel 5 0 2 v)
theorem sourceMap1037_checked : acceptsGraphIso
    (source (graph core1037) (root 5) 0 2) DegreeOneSmallSpectrum088.graph sourceMap1037=true := by decide +kernel
theorem fusedMap1037_checked : acceptsGraphIso
    (fused (graph core1037) (root 5) 0 2) DegreeOneSmallSpectrum091.graph fusedMap1037=true := by decide +kernel
theorem certified1037 : Certified (graph core1037) (root 5) 0 2 :=
  of_native_maps core1037 DegreeOneSmallSpectrum088.graph DegreeOneSmallSpectrum091.graph
    sourceMap1037 fusedMap1037 sourceMap1037_checked fusedMap1037_checked
    DegreeTwoThreeFiniteComparisons.comparison1037
#print axioms sourceMap1037_checked
#print axioms fusedMap1037_checked
#print axioms certified1037
def sourceMap1037swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,6,7,8,9,4,1,2,3,5] (sourceLabel 5 2 0 v)
def fusedMap1037swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,9,5,6,7,8] (fusedLabel 5 2 0 v)
theorem sourceMap1037swap_checked : acceptsGraphIso
    (source (graph core1037) (root 5) 2 0) DegreeOneSmallSpectrum088.graph sourceMap1037swap=true := by decide +kernel
theorem fusedMap1037swap_checked : acceptsGraphIso
    (fused (graph core1037) (root 5) 2 0) DegreeOneSmallSpectrum091.graph fusedMap1037swap=true := by decide +kernel
theorem certified1037swap : Certified (graph core1037) (root 5) 2 0 :=
  of_native_maps core1037 DegreeOneSmallSpectrum088.graph DegreeOneSmallSpectrum091.graph
    sourceMap1037swap fusedMap1037swap sourceMap1037swap_checked fusedMap1037swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1037
#print axioms sourceMap1037swap_checked
#print axioms fusedMap1037swap_checked
#print axioms certified1037swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

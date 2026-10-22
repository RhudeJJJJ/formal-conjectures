/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1046 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap1046 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,4,5,1,2,3] (sourceLabel 6 0 2 v)
def fusedMap1046 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (fusedLabel 6 0 2 v)
theorem sourceMap1046_checked : acceptsGraphIso
    (source (graph core1046) (root 6) 0 2) DegreeOneSmallSpectrum224.graph sourceMap1046=true := by decide +kernel
theorem fusedMap1046_checked : acceptsGraphIso
    (fused (graph core1046) (root 6) 0 2) DegreeOneSmallSpectrum227.graph fusedMap1046=true := by decide +kernel
theorem certified1046 : Certified (graph core1046) (root 6) 0 2 :=
  of_native_maps core1046 DegreeOneSmallSpectrum224.graph DegreeOneSmallSpectrum227.graph
    sourceMap1046 fusedMap1046 sourceMap1046_checked fusedMap1046_checked
    DegreeTwoThreeFiniteComparisons.comparison1046
#print axioms sourceMap1046_checked
#print axioms fusedMap1046_checked
#print axioms certified1046
def sourceMap1046swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,4,1,2,3,5] (sourceLabel 6 2 0 v)
def fusedMap1046swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (fusedLabel 6 2 0 v)
theorem sourceMap1046swap_checked : acceptsGraphIso
    (source (graph core1046) (root 6) 2 0) DegreeOneSmallSpectrum224.graph sourceMap1046swap=true := by decide +kernel
theorem fusedMap1046swap_checked : acceptsGraphIso
    (fused (graph core1046) (root 6) 2 0) DegreeOneSmallSpectrum227.graph fusedMap1046swap=true := by decide +kernel
theorem certified1046swap : Certified (graph core1046) (root 6) 2 0 :=
  of_native_maps core1046 DegreeOneSmallSpectrum224.graph DegreeOneSmallSpectrum227.graph
    sourceMap1046swap fusedMap1046swap sourceMap1046swap_checked fusedMap1046swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1046
#print axioms sourceMap1046swap_checked
#print axioms fusedMap1046swap_checked
#print axioms certified1046swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

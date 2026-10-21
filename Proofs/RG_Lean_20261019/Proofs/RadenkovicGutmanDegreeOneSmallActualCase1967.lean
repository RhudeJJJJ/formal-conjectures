/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1967 : Family 10 := level10.get ⟨285,by decide⟩
def sourceMap1967 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1967 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1967_checked : acceptsGraphIso
    (source (graph core1967) (root 10) 0 0) DegreeOneSmallSpectrum1251.graph sourceMap1967=true := by decide +kernel
theorem fusedMap1967_checked : acceptsGraphIso
    (fused (graph core1967) (root 10) 0 0) DegreeOneSmallSpectrum1301.graph fusedMap1967=true := by decide +kernel
theorem certified1967 : Certified (graph core1967) (root 10) 0 0 :=
  of_native_maps core1967 DegreeOneSmallSpectrum1251.graph DegreeOneSmallSpectrum1301.graph
    sourceMap1967 fusedMap1967 sourceMap1967_checked fusedMap1967_checked
    DegreeOneSmallComparisons.comparison1967
#print axioms sourceMap1967_checked
#print axioms fusedMap1967_checked
#print axioms certified1967
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

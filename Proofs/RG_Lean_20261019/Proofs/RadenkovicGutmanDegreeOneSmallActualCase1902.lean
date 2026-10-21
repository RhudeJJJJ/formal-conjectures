/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1902 : Family 10 := level10.get ⟨179,by decide⟩
def sourceMap1902 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,6,7,8,4,5] (sourceLabel 10 0 0 v)
def fusedMap1902 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1902_checked : acceptsGraphIso
    (source (graph core1902) (root 10) 0 0) DegreeOneSmallSpectrum1095.graph sourceMap1902=true := by decide +kernel
theorem fusedMap1902_checked : acceptsGraphIso
    (fused (graph core1902) (root 10) 0 0) DegreeOneSmallSpectrum947.graph fusedMap1902=true := by decide +kernel
theorem certified1902 : Certified (graph core1902) (root 10) 0 0 :=
  of_native_maps core1902 DegreeOneSmallSpectrum1095.graph DegreeOneSmallSpectrum947.graph
    sourceMap1902 fusedMap1902 sourceMap1902_checked fusedMap1902_checked
    DegreeOneSmallComparisons.comparison1902
#print axioms sourceMap1902_checked
#print axioms fusedMap1902_checked
#print axioms certified1902
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

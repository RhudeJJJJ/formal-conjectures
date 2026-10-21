/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1909 : Family 10 := level10.get ⟨195,by decide⟩
def sourceMap1909 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1909 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1909_checked : acceptsGraphIso
    (source (graph core1909) (root 10) 0 0) DegreeOneSmallSpectrum1012.graph sourceMap1909=true := by decide +kernel
theorem fusedMap1909_checked : acceptsGraphIso
    (fused (graph core1909) (root 10) 0 0) DegreeOneSmallSpectrum1015.graph fusedMap1909=true := by decide +kernel
theorem certified1909 : Certified (graph core1909) (root 10) 0 0 :=
  of_native_maps core1909 DegreeOneSmallSpectrum1012.graph DegreeOneSmallSpectrum1015.graph
    sourceMap1909 fusedMap1909 sourceMap1909_checked fusedMap1909_checked
    DegreeOneSmallComparisons.comparison1909
#print axioms sourceMap1909_checked
#print axioms fusedMap1909_checked
#print axioms certified1909
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

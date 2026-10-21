/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1943 : Family 10 := level10.get ⟨242,by decide⟩
def sourceMap1943 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1943 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1943_checked : acceptsGraphIso
    (source (graph core1943) (root 10) 0 0) DegreeOneSmallSpectrum1198.graph sourceMap1943=true := by decide +kernel
theorem fusedMap1943_checked : acceptsGraphIso
    (fused (graph core1943) (root 10) 0 0) DegreeOneSmallSpectrum1201.graph fusedMap1943=true := by decide +kernel
theorem certified1943 : Certified (graph core1943) (root 10) 0 0 :=
  of_native_maps core1943 DegreeOneSmallSpectrum1198.graph DegreeOneSmallSpectrum1201.graph
    sourceMap1943 fusedMap1943 sourceMap1943_checked fusedMap1943_checked
    DegreeOneSmallComparisons.comparison1943
#print axioms sourceMap1943_checked
#print axioms fusedMap1943_checked
#print axioms certified1943
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

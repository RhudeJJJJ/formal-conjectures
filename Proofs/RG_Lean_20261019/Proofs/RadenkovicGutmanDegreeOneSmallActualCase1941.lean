/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1941 : Family 10 := level10.get ⟨240,by decide⟩
def sourceMap1941 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1941 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1941_checked : acceptsGraphIso
    (source (graph core1941) (root 10) 0 0) DegreeOneSmallSpectrum1186.graph sourceMap1941=true := by decide +kernel
theorem fusedMap1941_checked : acceptsGraphIso
    (fused (graph core1941) (root 10) 0 0) DegreeOneSmallSpectrum1189.graph fusedMap1941=true := by decide +kernel
theorem certified1941 : Certified (graph core1941) (root 10) 0 0 :=
  of_native_maps core1941 DegreeOneSmallSpectrum1186.graph DegreeOneSmallSpectrum1189.graph
    sourceMap1941 fusedMap1941 sourceMap1941_checked fusedMap1941_checked
    DegreeOneSmallComparisons.comparison1941
#print axioms sourceMap1941_checked
#print axioms fusedMap1941_checked
#print axioms certified1941
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

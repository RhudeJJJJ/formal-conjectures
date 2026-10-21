/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1938 : Family 10 := level10.get ⟨233,by decide⟩
def sourceMap1938 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1938 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1938_checked : acceptsGraphIso
    (source (graph core1938) (root 10) 0 0) DegreeOneSmallSpectrum1148.graph sourceMap1938=true := by decide +kernel
theorem fusedMap1938_checked : acceptsGraphIso
    (fused (graph core1938) (root 10) 0 0) DegreeOneSmallSpectrum1180.graph fusedMap1938=true := by decide +kernel
theorem certified1938 : Certified (graph core1938) (root 10) 0 0 :=
  of_native_maps core1938 DegreeOneSmallSpectrum1148.graph DegreeOneSmallSpectrum1180.graph
    sourceMap1938 fusedMap1938 sourceMap1938_checked fusedMap1938_checked
    DegreeOneSmallComparisons.comparison1938
#print axioms sourceMap1938_checked
#print axioms fusedMap1938_checked
#print axioms certified1938
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1971 : Family 10 := level10.get ⟨290,by decide⟩
def sourceMap1971 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1971 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1971_checked : acceptsGraphIso
    (source (graph core1971) (root 10) 0 0) DegreeOneSmallSpectrum1254.graph sourceMap1971=true := by decide +kernel
theorem fusedMap1971_checked : acceptsGraphIso
    (fused (graph core1971) (root 10) 0 0) DegreeOneSmallSpectrum1319.graph fusedMap1971=true := by decide +kernel
theorem certified1971 : Certified (graph core1971) (root 10) 0 0 :=
  of_native_maps core1971 DegreeOneSmallSpectrum1254.graph DegreeOneSmallSpectrum1319.graph
    sourceMap1971 fusedMap1971 sourceMap1971_checked fusedMap1971_checked
    DegreeOneSmallComparisons.comparison1971
#print axioms sourceMap1971_checked
#print axioms fusedMap1971_checked
#print axioms certified1971
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

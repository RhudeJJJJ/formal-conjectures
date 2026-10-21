/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1923 : Family 10 := level10.get ⟨215,by decide⟩
def sourceMap1923 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1923 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1923_checked : acceptsGraphIso
    (source (graph core1923) (root 10) 0 0) DegreeOneSmallSpectrum1085.graph sourceMap1923=true := by decide +kernel
theorem fusedMap1923_checked : acceptsGraphIso
    (fused (graph core1923) (root 10) 0 0) DegreeOneSmallSpectrum1088.graph fusedMap1923=true := by decide +kernel
theorem certified1923 : Certified (graph core1923) (root 10) 0 0 :=
  of_native_maps core1923 DegreeOneSmallSpectrum1085.graph DegreeOneSmallSpectrum1088.graph
    sourceMap1923 fusedMap1923 sourceMap1923_checked fusedMap1923_checked
    DegreeOneSmallComparisons.comparison1923
#print axioms sourceMap1923_checked
#print axioms fusedMap1923_checked
#print axioms certified1923
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

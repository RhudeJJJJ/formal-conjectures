/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1889 : Family 10 := level10.get ⟨157,by decide⟩
def sourceMap1889 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1889 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1889_checked : acceptsGraphIso
    (source (graph core1889) (root 10) 0 0) DegreeOneSmallSpectrum1158.graph sourceMap1889=true := by decide +kernel
theorem fusedMap1889_checked : acceptsGraphIso
    (fused (graph core1889) (root 10) 0 0) DegreeOneSmallSpectrum960.graph fusedMap1889=true := by decide +kernel
theorem certified1889 : Certified (graph core1889) (root 10) 0 0 :=
  of_native_maps core1889 DegreeOneSmallSpectrum1158.graph DegreeOneSmallSpectrum960.graph
    sourceMap1889 fusedMap1889 sourceMap1889_checked fusedMap1889_checked
    DegreeOneSmallComparisons.comparison1889
#print axioms sourceMap1889_checked
#print axioms fusedMap1889_checked
#print axioms certified1889
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

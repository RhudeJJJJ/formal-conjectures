/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1847 : Family 10 := level10.get ⟨100,by decide⟩
def sourceMap1847 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1847 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1847_checked : acceptsGraphIso
    (source (graph core1847) (root 10) 0 0) DegreeOneSmallSpectrum1270.graph sourceMap1847=true := by decide +kernel
theorem fusedMap1847_checked : acceptsGraphIso
    (fused (graph core1847) (root 10) 0 0) DegreeOneSmallSpectrum924.graph fusedMap1847=true := by decide +kernel
theorem certified1847 : Certified (graph core1847) (root 10) 0 0 :=
  of_native_maps core1847 DegreeOneSmallSpectrum1270.graph DegreeOneSmallSpectrum924.graph
    sourceMap1847 fusedMap1847 sourceMap1847_checked fusedMap1847_checked
    DegreeOneSmallComparisons.comparison1847
#print axioms sourceMap1847_checked
#print axioms fusedMap1847_checked
#print axioms certified1847
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

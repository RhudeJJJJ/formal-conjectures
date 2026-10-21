/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1786 : Family 10 := level10.get ⟨21,by decide⟩
def sourceMap1786 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1786 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1786_checked : acceptsGraphIso
    (source (graph core1786) (root 10) 0 0) DegreeOneSmallSpectrum899.graph sourceMap1786=true := by decide +kernel
theorem fusedMap1786_checked : acceptsGraphIso
    (fused (graph core1786) (root 10) 0 0) DegreeOneSmallSpectrum935.graph fusedMap1786=true := by decide +kernel
theorem certified1786 : Certified (graph core1786) (root 10) 0 0 :=
  of_native_maps core1786 DegreeOneSmallSpectrum899.graph DegreeOneSmallSpectrum935.graph
    sourceMap1786 fusedMap1786 sourceMap1786_checked fusedMap1786_checked
    DegreeOneSmallComparisons.comparison1786
#print axioms sourceMap1786_checked
#print axioms fusedMap1786_checked
#print axioms certified1786
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

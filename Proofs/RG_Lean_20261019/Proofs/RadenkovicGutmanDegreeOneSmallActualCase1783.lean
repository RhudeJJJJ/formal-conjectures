/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1783 : Family 10 := level10.get ⟨18,by decide⟩
def sourceMap1783 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1783 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1783_checked : acceptsGraphIso
    (source (graph core1783) (root 10) 0 0) DegreeOneSmallSpectrum896.graph sourceMap1783=true := by decide +kernel
theorem fusedMap1783_checked : acceptsGraphIso
    (fused (graph core1783) (root 10) 0 0) DegreeOneSmallSpectrum915.graph fusedMap1783=true := by decide +kernel
theorem certified1783 : Certified (graph core1783) (root 10) 0 0 :=
  of_native_maps core1783 DegreeOneSmallSpectrum896.graph DegreeOneSmallSpectrum915.graph
    sourceMap1783 fusedMap1783 sourceMap1783_checked fusedMap1783_checked
    DegreeOneSmallComparisons.comparison1783
#print axioms sourceMap1783_checked
#print axioms fusedMap1783_checked
#print axioms certified1783
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

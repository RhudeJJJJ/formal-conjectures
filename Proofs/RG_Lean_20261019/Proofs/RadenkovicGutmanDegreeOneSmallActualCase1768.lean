/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1768 : Family 10 := level10.get ⟨1,by decide⟩
def sourceMap1768 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (sourceLabel 10 0 0 v)
def fusedMap1768 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1768_checked : acceptsGraphIso
    (source (graph core1768) (root 10) 0 0) DegreeOneSmallSpectrum895.graph sourceMap1768=true := by decide +kernel
theorem fusedMap1768_checked : acceptsGraphIso
    (fused (graph core1768) (root 10) 0 0) DegreeOneSmallSpectrum856.graph fusedMap1768=true := by decide +kernel
theorem certified1768 : Certified (graph core1768) (root 10) 0 0 :=
  of_native_maps core1768 DegreeOneSmallSpectrum895.graph DegreeOneSmallSpectrum856.graph
    sourceMap1768 fusedMap1768 sourceMap1768_checked fusedMap1768_checked
    DegreeOneSmallComparisons.comparison1768
#print axioms sourceMap1768_checked
#print axioms fusedMap1768_checked
#print axioms certified1768
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0069 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0069 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 3 2 2 v)
def fusedMap0069 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![1,2,3,4,0,5,6,7,8,9] (fusedLabel 3 2 2 v)
theorem sourceMap0069_checked : acceptsGraphIso
    (source (graph core0069) (root 3) 2 2) DegreeOneSmallSpectrum146.graph sourceMap0069=true := by decide +kernel
theorem fusedMap0069_checked : acceptsGraphIso
    (fused (graph core0069) (root 3) 2 2) DegreeOneSmallSpectrum073.graph fusedMap0069=true := by decide +kernel
theorem certified0069 : Certified (graph core0069) (root 3) 2 2 :=
  of_native_maps core0069 DegreeOneSmallSpectrum146.graph DegreeOneSmallSpectrum073.graph
    sourceMap0069 fusedMap0069 sourceMap0069_checked fusedMap0069_checked
    DegreeOneSmallComparisons.comparison0069
#print axioms sourceMap0069_checked
#print axioms fusedMap0069_checked
#print axioms certified0069
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

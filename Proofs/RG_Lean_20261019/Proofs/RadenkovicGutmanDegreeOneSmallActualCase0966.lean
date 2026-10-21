/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0966 : Family 8 := level8.get ⟨79,by decide⟩
def sourceMap0966 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0966 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0966_checked : acceptsGraphIso
    (source (graph core0966) (root 8) 1 1) DegreeOneSmallSpectrum1322.graph sourceMap0966=true := by decide +kernel
theorem fusedMap0966_checked : acceptsGraphIso
    (fused (graph core0966) (root 8) 1 1) DegreeOneSmallSpectrum958.graph fusedMap0966=true := by decide +kernel
theorem certified0966 : Certified (graph core0966) (root 8) 1 1 :=
  of_native_maps core0966 DegreeOneSmallSpectrum1322.graph DegreeOneSmallSpectrum958.graph
    sourceMap0966 fusedMap0966 sourceMap0966_checked fusedMap0966_checked
    DegreeOneSmallComparisons.comparison0966
#print axioms sourceMap0966_checked
#print axioms fusedMap0966_checked
#print axioms certified0966
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

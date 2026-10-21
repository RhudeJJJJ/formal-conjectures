/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0054 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0054 : (Vertices 2 ⊕ Fin 5 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,11,12,1,2,3,4,5,6,7,8,9,10] (sourceLabel 2 4 4 v)
def fusedMap0054 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 4 4 v)
theorem sourceMap0054_checked : acceptsGraphIso
    (source (graph core0054) (root 2) 4 4) DegreeOneSmallSpectrum977.graph sourceMap0054=true := by decide +kernel
theorem fusedMap0054_checked : acceptsGraphIso
    (fused (graph core0054) (root 2) 4 4) DegreeOneSmallSpectrum861.graph fusedMap0054=true := by decide +kernel
theorem certified0054 : Certified (graph core0054) (root 2) 4 4 :=
  of_native_maps core0054 DegreeOneSmallSpectrum977.graph DegreeOneSmallSpectrum861.graph
    sourceMap0054 fusedMap0054 sourceMap0054_checked fusedMap0054_checked
    DegreeOneSmallComparisons.comparison0054
#print axioms sourceMap0054_checked
#print axioms fusedMap0054_checked
#print axioms certified0054
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0923 : Family 8 := level8.get ⟨63,by decide⟩
def sourceMap0923 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0923 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0923_checked : acceptsGraphIso
    (source (graph core0923) (root 8) 0 0) DegreeOneSmallSpectrum298.graph sourceMap0923=true := by decide +kernel
theorem fusedMap0923_checked : acceptsGraphIso
    (fused (graph core0923) (root 8) 0 0) DegreeOneSmallSpectrum211.graph fusedMap0923=true := by decide +kernel
theorem certified0923 : Certified (graph core0923) (root 8) 0 0 :=
  of_native_maps core0923 DegreeOneSmallSpectrum298.graph DegreeOneSmallSpectrum211.graph
    sourceMap0923 fusedMap0923 sourceMap0923_checked fusedMap0923_checked
    DegreeOneSmallComparisons.comparison0923
#print axioms sourceMap0923_checked
#print axioms fusedMap0923_checked
#print axioms certified0923
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

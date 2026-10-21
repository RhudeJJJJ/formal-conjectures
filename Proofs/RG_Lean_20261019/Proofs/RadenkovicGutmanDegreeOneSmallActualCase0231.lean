/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0231 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0231 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,4,5,6,7,2,3] (sourceLabel 5 0 0 v)
def fusedMap0231 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0231_checked : acceptsGraphIso
    (source (graph core0231) (root 5) 0 0) DegreeOneSmallSpectrum032.graph sourceMap0231=true := by decide +kernel
theorem fusedMap0231_checked : acceptsGraphIso
    (fused (graph core0231) (root 5) 0 0) DegreeOneSmallSpectrum022.graph fusedMap0231=true := by decide +kernel
theorem certified0231 : Certified (graph core0231) (root 5) 0 0 :=
  of_native_maps core0231 DegreeOneSmallSpectrum032.graph DegreeOneSmallSpectrum022.graph
    sourceMap0231 fusedMap0231 sourceMap0231_checked fusedMap0231_checked
    DegreeOneSmallComparisons.comparison0231
#print axioms sourceMap0231_checked
#print axioms fusedMap0231_checked
#print axioms certified0231
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

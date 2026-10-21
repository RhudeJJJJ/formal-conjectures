/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0681 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0681 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (sourceLabel 7 0 0 v)
def fusedMap0681 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0681_checked : acceptsGraphIso
    (source (graph core0681) (root 7) 0 0) DegreeOneSmallSpectrum156.graph sourceMap0681=true := by decide +kernel
theorem fusedMap0681_checked : acceptsGraphIso
    (fused (graph core0681) (root 7) 0 0) DegreeOneSmallSpectrum097.graph fusedMap0681=true := by decide +kernel
theorem certified0681 : Certified (graph core0681) (root 7) 0 0 :=
  of_native_maps core0681 DegreeOneSmallSpectrum156.graph DegreeOneSmallSpectrum097.graph
    sourceMap0681 fusedMap0681 sourceMap0681_checked fusedMap0681_checked
    DegreeOneSmallComparisons.comparison0681
#print axioms sourceMap0681_checked
#print axioms fusedMap0681_checked
#print axioms certified0681
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0615 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0615 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 7 0 0 v)
def fusedMap0615 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0615_checked : acceptsGraphIso
    (source (graph core0615) (root 7) 0 0) DegreeOneSmallSpectrum118.graph sourceMap0615=true := by decide +kernel
theorem fusedMap0615_checked : acceptsGraphIso
    (fused (graph core0615) (root 7) 0 0) DegreeOneSmallSpectrum137.graph fusedMap0615=true := by decide +kernel
theorem certified0615 : Certified (graph core0615) (root 7) 0 0 :=
  of_native_maps core0615 DegreeOneSmallSpectrum118.graph DegreeOneSmallSpectrum137.graph
    sourceMap0615 fusedMap0615 sourceMap0615_checked fusedMap0615_checked
    DegreeOneSmallComparisons.comparison0615
#print axioms sourceMap0615_checked
#print axioms fusedMap0615_checked
#print axioms certified0615
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

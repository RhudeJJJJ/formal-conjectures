/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0543 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0543 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (sourceLabel 7 0 0 v)
def fusedMap0543 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0543_checked : acceptsGraphIso
    (source (graph core0543) (root 7) 0 0) DegreeOneSmallSpectrum121.graph sourceMap0543=true := by decide +kernel
theorem fusedMap0543_checked : acceptsGraphIso
    (fused (graph core0543) (root 7) 0 0) DegreeOneSmallSpectrum089.graph fusedMap0543=true := by decide +kernel
theorem certified0543 : Certified (graph core0543) (root 7) 0 0 :=
  of_native_maps core0543 DegreeOneSmallSpectrum121.graph DegreeOneSmallSpectrum089.graph
    sourceMap0543 fusedMap0543 sourceMap0543_checked fusedMap0543_checked
    DegreeOneSmallComparisons.comparison0543
#print axioms sourceMap0543_checked
#print axioms fusedMap0543_checked
#print axioms certified0543
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0411 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0411 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (sourceLabel 6 0 0 v)
def fusedMap0411 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0411_checked : acceptsGraphIso
    (source (graph core0411) (root 6) 0 0) DegreeOneSmallSpectrum070.graph sourceMap0411=true := by decide +kernel
theorem fusedMap0411_checked : acceptsGraphIso
    (fused (graph core0411) (root 6) 0 0) DegreeOneSmallSpectrum044.graph fusedMap0411=true := by decide +kernel
theorem certified0411 : Certified (graph core0411) (root 6) 0 0 :=
  of_native_maps core0411 DegreeOneSmallSpectrum070.graph DegreeOneSmallSpectrum044.graph
    sourceMap0411 fusedMap0411 sourceMap0411_checked fusedMap0411_checked
    DegreeOneSmallComparisons.comparison0411
#print axioms sourceMap0411_checked
#print axioms fusedMap0411_checked
#print axioms certified0411
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

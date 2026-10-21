/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0882 : Family 8 := level8.get ⟨46,by decide⟩
def sourceMap0882 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap0882 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0882_checked : acceptsGraphIso
    (source (graph core0882) (root 8) 1 1) DegreeOneSmallSpectrum1230.graph sourceMap0882=true := by decide +kernel
theorem fusedMap0882_checked : acceptsGraphIso
    (fused (graph core0882) (root 8) 1 1) DegreeOneSmallSpectrum882.graph fusedMap0882=true := by decide +kernel
theorem certified0882 : Certified (graph core0882) (root 8) 1 1 :=
  of_native_maps core0882 DegreeOneSmallSpectrum1230.graph DegreeOneSmallSpectrum882.graph
    sourceMap0882 fusedMap0882 sourceMap0882_checked fusedMap0882_checked
    DegreeOneSmallComparisons.comparison0882
#print axioms sourceMap0882_checked
#print axioms fusedMap0882_checked
#print axioms certified0882
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

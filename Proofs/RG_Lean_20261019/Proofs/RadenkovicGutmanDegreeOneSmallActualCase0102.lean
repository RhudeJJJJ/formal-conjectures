/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0102 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0102 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,6,7,8,2,3,4,5] (sourceLabel 4 1 1 v)
def fusedMap0102 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap0102_checked : acceptsGraphIso
    (source (graph core0102) (root 4) 1 1) DegreeOneSmallSpectrum055.graph sourceMap0102=true := by decide +kernel
theorem fusedMap0102_checked : acceptsGraphIso
    (fused (graph core0102) (root 4) 1 1) DegreeOneSmallSpectrum037.graph fusedMap0102=true := by decide +kernel
theorem certified0102 : Certified (graph core0102) (root 4) 1 1 :=
  of_native_maps core0102 DegreeOneSmallSpectrum055.graph DegreeOneSmallSpectrum037.graph
    sourceMap0102 fusedMap0102 sourceMap0102_checked fusedMap0102_checked
    DegreeOneSmallComparisons.comparison0102
#print axioms sourceMap0102_checked
#print axioms fusedMap0102_checked
#print axioms certified0102
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

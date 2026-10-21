/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0366 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0366 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,4,5,2,3] (sourceLabel 6 0 0 v)
def fusedMap0366 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap0366_checked : acceptsGraphIso
    (source (graph core0366) (root 6) 0 0) DegreeOneSmallSpectrum043.graph sourceMap0366=true := by decide +kernel
theorem fusedMap0366_checked : acceptsGraphIso
    (fused (graph core0366) (root 6) 0 0) DegreeOneSmallSpectrum061.graph fusedMap0366=true := by decide +kernel
theorem certified0366 : Certified (graph core0366) (root 6) 0 0 :=
  of_native_maps core0366 DegreeOneSmallSpectrum043.graph DegreeOneSmallSpectrum061.graph
    sourceMap0366 fusedMap0366 sourceMap0366_checked fusedMap0366_checked
    DegreeOneSmallComparisons.comparison0366
#print axioms sourceMap0366_checked
#print axioms fusedMap0366_checked
#print axioms certified0366
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

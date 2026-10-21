/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0419 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0419 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0419 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0419_checked : acceptsGraphIso
    (source (graph core0419) (root 6) 2 2) DegreeOneSmallSpectrum1807.graph sourceMap0419=true := by decide +kernel
theorem fusedMap0419_checked : acceptsGraphIso
    (fused (graph core0419) (root 6) 2 2) DegreeOneSmallSpectrum872.graph fusedMap0419=true := by decide +kernel
theorem certified0419 : Certified (graph core0419) (root 6) 2 2 :=
  of_native_maps core0419 DegreeOneSmallSpectrum1807.graph DegreeOneSmallSpectrum872.graph
    sourceMap0419 fusedMap0419 sourceMap0419_checked fusedMap0419_checked
    DegreeOneSmallComparisons.comparison0419
#print axioms sourceMap0419_checked
#print axioms fusedMap0419_checked
#print axioms certified0419
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

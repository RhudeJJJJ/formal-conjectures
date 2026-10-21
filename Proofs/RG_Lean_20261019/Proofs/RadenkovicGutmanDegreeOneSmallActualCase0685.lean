/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0685 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0685 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0685 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0685_checked : acceptsGraphIso
    (source (graph core0685) (root 7) 1 1) DegreeOneSmallSpectrum638.graph sourceMap0685=true := by decide +kernel
theorem fusedMap0685_checked : acceptsGraphIso
    (fused (graph core0685) (root 7) 1 1) DegreeOneSmallSpectrum405.graph fusedMap0685=true := by decide +kernel
theorem certified0685 : Certified (graph core0685) (root 7) 1 1 :=
  of_native_maps core0685 DegreeOneSmallSpectrum638.graph DegreeOneSmallSpectrum405.graph
    sourceMap0685 fusedMap0685 sourceMap0685_checked fusedMap0685_checked
    DegreeOneSmallComparisons.comparison0685
#print axioms sourceMap0685_checked
#print axioms fusedMap0685_checked
#print axioms certified0685
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

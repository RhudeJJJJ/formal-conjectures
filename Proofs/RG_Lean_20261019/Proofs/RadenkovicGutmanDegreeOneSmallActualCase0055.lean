/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0055 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0055 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 1) → Fin 6 :=
  fun v => ![1,0,4,5,2,3] (sourceLabel 3 0 0 v)
def fusedMap0055 : (Vertices 3 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,3,4,5,1,2] (fusedLabel 3 0 0 v)
theorem sourceMap0055_checked : acceptsGraphIso
    (source (graph core0055) (root 3) 0 0) DegreeOneSmallSpectrum006.graph sourceMap0055=true := by decide +kernel
theorem fusedMap0055_checked : acceptsGraphIso
    (fused (graph core0055) (root 3) 0 0) DegreeOneSmallSpectrum004.graph fusedMap0055=true := by decide +kernel
theorem certified0055 : Certified (graph core0055) (root 3) 0 0 :=
  of_native_maps core0055 DegreeOneSmallSpectrum006.graph DegreeOneSmallSpectrum004.graph
    sourceMap0055 fusedMap0055 sourceMap0055_checked fusedMap0055_checked
    DegreeOneSmallComparisons.comparison0055
#print axioms sourceMap0055_checked
#print axioms fusedMap0055_checked
#print axioms certified0055
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

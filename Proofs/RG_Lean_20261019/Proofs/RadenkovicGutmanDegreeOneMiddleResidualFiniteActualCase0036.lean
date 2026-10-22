/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0036 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0036 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap0036 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0036_checked : acceptsGraphIso
    (source (graph core0036) (root 7) 2 2) DegreeOneMiddleResidualSpectrum088.graph sourceMap0036=true := by decide +kernel
theorem fusedMap0036_checked : acceptsGraphIso
    (fused (graph core0036) (root 7) 2 2) DegreeOneMiddleResidualSpectrum053.graph fusedMap0036=true := by decide +kernel
theorem certified0036 : Certified (graph core0036) (root 7) 2 2 :=
  of_native_maps core0036 DegreeOneMiddleResidualSpectrum088.graph DegreeOneMiddleResidualSpectrum053.graph
    sourceMap0036 fusedMap0036 sourceMap0036_checked fusedMap0036_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0036
#print axioms sourceMap0036_checked
#print axioms fusedMap0036_checked
#print axioms certified0036
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

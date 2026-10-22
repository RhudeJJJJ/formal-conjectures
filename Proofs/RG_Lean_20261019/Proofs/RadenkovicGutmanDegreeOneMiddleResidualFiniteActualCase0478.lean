/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0478 : Family 9 := level9.get ⟨600,by decide⟩
def sourceMap0478 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0478 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0478_checked : acceptsGraphIso
    (source (graph core0478) (root 9) 2 2) DegreeOneMiddleResidualSpectrum922.graph sourceMap0478=true := by decide +kernel
theorem fusedMap0478_checked : acceptsGraphIso
    (fused (graph core0478) (root 9) 2 2) DegreeOneMiddleResidualSpectrum601.graph fusedMap0478=true := by decide +kernel
theorem certified0478 : Certified (graph core0478) (root 9) 2 2 :=
  of_native_maps core0478 DegreeOneMiddleResidualSpectrum922.graph DegreeOneMiddleResidualSpectrum601.graph
    sourceMap0478 fusedMap0478 sourceMap0478_checked fusedMap0478_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0478
#print axioms sourceMap0478_checked
#print axioms fusedMap0478_checked
#print axioms certified0478
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

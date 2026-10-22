/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0261 : Family 9 := level9.get ⟨81,by decide⟩
def sourceMap0261 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0261 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0261_checked : acceptsGraphIso
    (source (graph core0261) (root 9) 2 2) DegreeOneMiddleResidualSpectrum677.graph sourceMap0261=true := by decide +kernel
theorem fusedMap0261_checked : acceptsGraphIso
    (fused (graph core0261) (root 9) 2 2) DegreeTwoThreeSpectrum4030.graph fusedMap0261=true := by decide +kernel
theorem certified0261 : Certified (graph core0261) (root 9) 2 2 :=
  of_native_maps core0261 DegreeOneMiddleResidualSpectrum677.graph DegreeTwoThreeSpectrum4030.graph
    sourceMap0261 fusedMap0261 sourceMap0261_checked fusedMap0261_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0261
#print axioms sourceMap0261_checked
#print axioms fusedMap0261_checked
#print axioms certified0261
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

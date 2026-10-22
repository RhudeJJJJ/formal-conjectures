/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0125 : Family 8 := level8.get ⟨100,by decide⟩
def sourceMap0125 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0125 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0125_checked : acceptsGraphIso
    (source (graph core0125) (root 8) 2 2) DegreeOneMiddleResidualSpectrum268.graph sourceMap0125=true := by decide +kernel
theorem fusedMap0125_checked : acceptsGraphIso
    (fused (graph core0125) (root 8) 2 2) DegreeTwoThreeSpectrum2462.graph fusedMap0125=true := by decide +kernel
theorem certified0125 : Certified (graph core0125) (root 8) 2 2 :=
  of_native_maps core0125 DegreeOneMiddleResidualSpectrum268.graph DegreeTwoThreeSpectrum2462.graph
    sourceMap0125 fusedMap0125 sourceMap0125_checked fusedMap0125_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0125
#print axioms sourceMap0125_checked
#print axioms fusedMap0125_checked
#print axioms certified0125
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

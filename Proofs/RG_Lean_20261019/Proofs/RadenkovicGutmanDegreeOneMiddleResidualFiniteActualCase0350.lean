/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0350 : Family 9 := level9.get ⟨229,by decide⟩
def sourceMap0350 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0350 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0350_checked : acceptsGraphIso
    (source (graph core0350) (root 9) 2 2) DegreeOneMiddleResidualSpectrum860.graph sourceMap0350=true := by decide +kernel
theorem fusedMap0350_checked : acceptsGraphIso
    (fused (graph core0350) (root 9) 2 2) DegreeTwoThreeSpectrum4021.graph fusedMap0350=true := by decide +kernel
theorem certified0350 : Certified (graph core0350) (root 9) 2 2 :=
  of_native_maps core0350 DegreeOneMiddleResidualSpectrum860.graph DegreeTwoThreeSpectrum4021.graph
    sourceMap0350 fusedMap0350 sourceMap0350_checked fusedMap0350_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0350
#print axioms sourceMap0350_checked
#print axioms fusedMap0350_checked
#print axioms certified0350
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

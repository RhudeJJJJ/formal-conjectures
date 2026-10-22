/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0607 : Family 10 := level10.get ⟨159,by decide⟩
def sourceMap0607 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0607 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0607_checked : acceptsGraphIso
    (source (graph core0607) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1860.graph sourceMap0607=true := by decide +kernel
theorem fusedMap0607_checked : acceptsGraphIso
    (fused (graph core0607) (root 10) 2 2) DegreeTwoThreeSpectrum5097.graph fusedMap0607=true := by decide +kernel
theorem certified0607 : Certified (graph core0607) (root 10) 2 2 :=
  of_native_maps core0607 DegreeOneMiddleResidualSpectrum1860.graph DegreeTwoThreeSpectrum5097.graph
    sourceMap0607 fusedMap0607 sourceMap0607_checked fusedMap0607_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0607
#print axioms sourceMap0607_checked
#print axioms fusedMap0607_checked
#print axioms certified0607
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

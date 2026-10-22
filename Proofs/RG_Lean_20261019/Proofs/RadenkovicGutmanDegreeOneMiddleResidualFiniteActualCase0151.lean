/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0151 : Family 8 := level8.get ⟨151,by decide⟩
def sourceMap0151 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0151 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0151_checked : acceptsGraphIso
    (source (graph core0151) (root 8) 2 2) DegreeOneMiddleResidualSpectrum317.graph sourceMap0151=true := by decide +kernel
theorem fusedMap0151_checked : acceptsGraphIso
    (fused (graph core0151) (root 8) 2 2) DegreeTwoThreeSpectrum2741.graph fusedMap0151=true := by decide +kernel
theorem certified0151 : Certified (graph core0151) (root 8) 2 2 :=
  of_native_maps core0151 DegreeOneMiddleResidualSpectrum317.graph DegreeTwoThreeSpectrum2741.graph
    sourceMap0151 fusedMap0151 sourceMap0151_checked fusedMap0151_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0151
#print axioms sourceMap0151_checked
#print axioms fusedMap0151_checked
#print axioms certified0151
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

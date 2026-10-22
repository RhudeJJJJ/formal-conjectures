/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0161 : Family 8 := level8.get ⟨191,by decide⟩
def sourceMap0161 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0161 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0161_checked : acceptsGraphIso
    (source (graph core0161) (root 8) 2 2) DegreeOneMiddleResidualSpectrum345.graph sourceMap0161=true := by decide +kernel
theorem fusedMap0161_checked : acceptsGraphIso
    (fused (graph core0161) (root 8) 2 2) DegreeTwoThreeSpectrum2440.graph fusedMap0161=true := by decide +kernel
theorem certified0161 : Certified (graph core0161) (root 8) 2 2 :=
  of_native_maps core0161 DegreeOneMiddleResidualSpectrum345.graph DegreeTwoThreeSpectrum2440.graph
    sourceMap0161 fusedMap0161 sourceMap0161_checked fusedMap0161_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0161
#print axioms sourceMap0161_checked
#print axioms fusedMap0161_checked
#print axioms certified0161
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

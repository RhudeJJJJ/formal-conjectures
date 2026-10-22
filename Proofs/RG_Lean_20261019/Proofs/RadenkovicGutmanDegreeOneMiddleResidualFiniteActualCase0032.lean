/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0032 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0032 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0032 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0032_checked : acceptsGraphIso
    (source (graph core0032) (root 7) 2 2) DegreeOneMiddleResidualSpectrum081.graph sourceMap0032=true := by decide +kernel
theorem fusedMap0032_checked : acceptsGraphIso
    (fused (graph core0032) (root 7) 2 2) DegreeTwoThreeSpectrum1836.graph fusedMap0032=true := by decide +kernel
theorem certified0032 : Certified (graph core0032) (root 7) 2 2 :=
  of_native_maps core0032 DegreeOneMiddleResidualSpectrum081.graph DegreeTwoThreeSpectrum1836.graph
    sourceMap0032 fusedMap0032 sourceMap0032_checked fusedMap0032_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0032
#print axioms sourceMap0032_checked
#print axioms fusedMap0032_checked
#print axioms certified0032
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

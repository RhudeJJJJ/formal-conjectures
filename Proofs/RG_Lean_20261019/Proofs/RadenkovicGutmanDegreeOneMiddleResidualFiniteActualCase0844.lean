/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0844 : Family 10 := level10.get ⟨566,by decide⟩
def sourceMap0844 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0844 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0844_checked : acceptsGraphIso
    (source (graph core0844) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2054.graph sourceMap0844=true := by decide +kernel
theorem fusedMap0844_checked : acceptsGraphIso
    (fused (graph core0844) (root 10) 2 2) DegreeTwoThreeSpectrum5230.graph fusedMap0844=true := by decide +kernel
theorem certified0844 : Certified (graph core0844) (root 10) 2 2 :=
  of_native_maps core0844 DegreeOneMiddleResidualSpectrum2054.graph DegreeTwoThreeSpectrum5230.graph
    sourceMap0844 fusedMap0844 sourceMap0844_checked fusedMap0844_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0844
#print axioms sourceMap0844_checked
#print axioms fusedMap0844_checked
#print axioms certified0844
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

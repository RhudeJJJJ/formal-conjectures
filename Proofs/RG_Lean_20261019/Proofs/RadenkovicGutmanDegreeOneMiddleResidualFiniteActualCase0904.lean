/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0904 : Family 10 := level10.get ⟨689,by decide⟩
def sourceMap0904 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0904 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0904_checked : acceptsGraphIso
    (source (graph core0904) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2156.graph sourceMap0904=true := by decide +kernel
theorem fusedMap0904_checked : acceptsGraphIso
    (fused (graph core0904) (root 10) 2 2) DegreeTwoThreeSpectrum5425.graph fusedMap0904=true := by decide +kernel
theorem certified0904 : Certified (graph core0904) (root 10) 2 2 :=
  of_native_maps core0904 DegreeOneMiddleResidualSpectrum2156.graph DegreeTwoThreeSpectrum5425.graph
    sourceMap0904 fusedMap0904 sourceMap0904_checked fusedMap0904_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0904
#print axioms sourceMap0904_checked
#print axioms fusedMap0904_checked
#print axioms certified0904
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

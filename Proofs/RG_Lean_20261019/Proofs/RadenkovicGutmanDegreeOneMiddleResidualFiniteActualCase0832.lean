/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0832 : Family 10 := level10.get ⟨542,by decide⟩
def sourceMap0832 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0832 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0832_checked : acceptsGraphIso
    (source (graph core0832) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2031.graph sourceMap0832=true := by decide +kernel
theorem fusedMap0832_checked : acceptsGraphIso
    (fused (graph core0832) (root 10) 2 2) DegreeTwoThreeSpectrum5192.graph fusedMap0832=true := by decide +kernel
theorem certified0832 : Certified (graph core0832) (root 10) 2 2 :=
  of_native_maps core0832 DegreeOneMiddleResidualSpectrum2031.graph DegreeTwoThreeSpectrum5192.graph
    sourceMap0832 fusedMap0832 sourceMap0832_checked fusedMap0832_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0832
#print axioms sourceMap0832_checked
#print axioms fusedMap0832_checked
#print axioms certified0832
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

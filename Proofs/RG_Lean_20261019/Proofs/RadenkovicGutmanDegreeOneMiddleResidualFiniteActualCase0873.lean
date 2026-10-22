/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0873 : Family 10 := level10.get ⟨618,by decide⟩
def sourceMap0873 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0873 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0873_checked : acceptsGraphIso
    (source (graph core0873) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2109.graph sourceMap0873=true := by decide +kernel
theorem fusedMap0873_checked : acceptsGraphIso
    (fused (graph core0873) (root 10) 2 2) DegreeTwoThreeSpectrum5308.graph fusedMap0873=true := by decide +kernel
theorem certified0873 : Certified (graph core0873) (root 10) 2 2 :=
  of_native_maps core0873 DegreeOneMiddleResidualSpectrum2109.graph DegreeTwoThreeSpectrum5308.graph
    sourceMap0873 fusedMap0873 sourceMap0873_checked fusedMap0873_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0873
#print axioms sourceMap0873_checked
#print axioms fusedMap0873_checked
#print axioms certified0873
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

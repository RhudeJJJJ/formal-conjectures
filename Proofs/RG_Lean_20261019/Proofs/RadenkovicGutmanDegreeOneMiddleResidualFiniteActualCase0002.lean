/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0002 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0002 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0002 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0002_checked : acceptsGraphIso
    (source (graph core0002) (root 7) 2 2) DegreeOneMiddleResidualSpectrum046.graph sourceMap0002=true := by decide +kernel
theorem fusedMap0002_checked : acceptsGraphIso
    (fused (graph core0002) (root 7) 2 2) DegreeTwoThreeSpectrum1722.graph fusedMap0002=true := by decide +kernel
theorem certified0002 : Certified (graph core0002) (root 7) 2 2 :=
  of_native_maps core0002 DegreeOneMiddleResidualSpectrum046.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap0002 fusedMap0002 sourceMap0002_checked fusedMap0002_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0002
#print axioms sourceMap0002_checked
#print axioms fusedMap0002_checked
#print axioms certified0002
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

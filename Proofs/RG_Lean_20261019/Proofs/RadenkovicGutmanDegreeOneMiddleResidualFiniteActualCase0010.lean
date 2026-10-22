/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0010 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0010 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0010 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0010_checked : acceptsGraphIso
    (source (graph core0010) (root 7) 2 2) DegreeOneMiddleResidualSpectrum075.graph sourceMap0010=true := by decide +kernel
theorem fusedMap0010_checked : acceptsGraphIso
    (fused (graph core0010) (root 7) 2 2) DegreeTwoThreeSpectrum1716.graph fusedMap0010=true := by decide +kernel
theorem certified0010 : Certified (graph core0010) (root 7) 2 2 :=
  of_native_maps core0010 DegreeOneMiddleResidualSpectrum075.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap0010 fusedMap0010 sourceMap0010_checked fusedMap0010_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0010
#print axioms sourceMap0010_checked
#print axioms fusedMap0010_checked
#print axioms certified0010
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

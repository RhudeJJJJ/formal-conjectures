/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0013 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0013 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap0013 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0013_checked : acceptsGraphIso
    (source (graph core0013) (root 7) 2 2) DegreeOneMiddleResidualSpectrum083.graph sourceMap0013=true := by decide +kernel
theorem fusedMap0013_checked : acceptsGraphIso
    (fused (graph core0013) (root 7) 2 2) DegreeTwoThreeSpectrum1719.graph fusedMap0013=true := by decide +kernel
theorem certified0013 : Certified (graph core0013) (root 7) 2 2 :=
  of_native_maps core0013 DegreeOneMiddleResidualSpectrum083.graph DegreeTwoThreeSpectrum1719.graph
    sourceMap0013 fusedMap0013 sourceMap0013_checked fusedMap0013_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0013
#print axioms sourceMap0013_checked
#print axioms fusedMap0013_checked
#print axioms certified0013
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

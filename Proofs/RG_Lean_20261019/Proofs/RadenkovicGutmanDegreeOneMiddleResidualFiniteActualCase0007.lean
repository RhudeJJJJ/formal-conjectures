/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0007 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0007 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0007 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0007_checked : acceptsGraphIso
    (source (graph core0007) (root 7) 2 2) DegreeOneMiddleResidualSpectrum067.graph sourceMap0007=true := by decide +kernel
theorem fusedMap0007_checked : acceptsGraphIso
    (fused (graph core0007) (root 7) 2 2) DegreeTwoThreeSpectrum1710.graph fusedMap0007=true := by decide +kernel
theorem certified0007 : Certified (graph core0007) (root 7) 2 2 :=
  of_native_maps core0007 DegreeOneMiddleResidualSpectrum067.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap0007 fusedMap0007 sourceMap0007_checked fusedMap0007_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0007
#print axioms sourceMap0007_checked
#print axioms fusedMap0007_checked
#print axioms certified0007
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

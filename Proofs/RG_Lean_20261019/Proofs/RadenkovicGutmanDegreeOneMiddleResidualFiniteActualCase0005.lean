/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0005 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0005 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,8,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0005 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0005_checked : acceptsGraphIso
    (source (graph core0005) (root 7) 2 2) DegreeOneMiddleResidualSpectrum047.graph sourceMap0005=true := by decide +kernel
theorem fusedMap0005_checked : acceptsGraphIso
    (fused (graph core0005) (root 7) 2 2) DegreeTwoThreeSpectrum1737.graph fusedMap0005=true := by decide +kernel
theorem certified0005 : Certified (graph core0005) (root 7) 2 2 :=
  of_native_maps core0005 DegreeOneMiddleResidualSpectrum047.graph DegreeTwoThreeSpectrum1737.graph
    sourceMap0005 fusedMap0005 sourceMap0005_checked fusedMap0005_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0005
#print axioms sourceMap0005_checked
#print axioms fusedMap0005_checked
#print axioms certified0005
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0001 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0001 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0001 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0001_checked : acceptsGraphIso
    (source (graph core0001) (root 7) 2 2) DegreeOneMiddleResidualSpectrum035.graph sourceMap0001=true := by decide +kernel
theorem fusedMap0001_checked : acceptsGraphIso
    (fused (graph core0001) (root 7) 2 2) DegreeTwoThreeSpectrum1715.graph fusedMap0001=true := by decide +kernel
theorem certified0001 : Certified (graph core0001) (root 7) 2 2 :=
  of_native_maps core0001 DegreeOneMiddleResidualSpectrum035.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap0001 fusedMap0001 sourceMap0001_checked fusedMap0001_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0001
#print axioms sourceMap0001_checked
#print axioms fusedMap0001_checked
#print axioms certified0001
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

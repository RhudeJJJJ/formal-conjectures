/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0012 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0012 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0012 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0012_checked : acceptsGraphIso
    (source (graph core0012) (root 7) 2 2) DegreeOneMiddleResidualSpectrum082.graph sourceMap0012=true := by decide +kernel
theorem fusedMap0012_checked : acceptsGraphIso
    (fused (graph core0012) (root 7) 2 2) DegreeTwoThreeSpectrum1718.graph fusedMap0012=true := by decide +kernel
theorem certified0012 : Certified (graph core0012) (root 7) 2 2 :=
  of_native_maps core0012 DegreeOneMiddleResidualSpectrum082.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap0012 fusedMap0012 sourceMap0012_checked fusedMap0012_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0012
#print axioms sourceMap0012_checked
#print axioms fusedMap0012_checked
#print axioms certified0012
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0011 : Family 7 := level7.get ⟨13,by decide⟩
def sourceMap0011 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0011 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0011_checked : acceptsGraphIso
    (source (graph core0011) (root 7) 2 2) DegreeOneMiddleResidualSpectrum079.graph sourceMap0011=true := by decide +kernel
theorem fusedMap0011_checked : acceptsGraphIso
    (fused (graph core0011) (root 7) 2 2) DegreeTwoThreeSpectrum1717.graph fusedMap0011=true := by decide +kernel
theorem certified0011 : Certified (graph core0011) (root 7) 2 2 :=
  of_native_maps core0011 DegreeOneMiddleResidualSpectrum079.graph DegreeTwoThreeSpectrum1717.graph
    sourceMap0011 fusedMap0011 sourceMap0011_checked fusedMap0011_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0011
#print axioms sourceMap0011_checked
#print axioms fusedMap0011_checked
#print axioms certified0011
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

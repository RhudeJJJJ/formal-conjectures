/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0030 : Family 7 := level7.get ⟨43,by decide⟩
def sourceMap0030 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0030 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0030_checked : acceptsGraphIso
    (source (graph core0030) (root 7) 2 2) DegreeOneMiddleResidualSpectrum078.graph sourceMap0030=true := by decide +kernel
theorem fusedMap0030_checked : acceptsGraphIso
    (fused (graph core0030) (root 7) 2 2) DegreeTwoThreeSpectrum1823.graph fusedMap0030=true := by decide +kernel
theorem certified0030 : Certified (graph core0030) (root 7) 2 2 :=
  of_native_maps core0030 DegreeOneMiddleResidualSpectrum078.graph DegreeTwoThreeSpectrum1823.graph
    sourceMap0030 fusedMap0030 sourceMap0030_checked fusedMap0030_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0030
#print axioms sourceMap0030_checked
#print axioms fusedMap0030_checked
#print axioms certified0030
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

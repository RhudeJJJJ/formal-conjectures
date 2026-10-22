/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0401 : Family 9 := level9.get ⟨342,by decide⟩
def sourceMap0401 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0401 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0401_checked : acceptsGraphIso
    (source (graph core0401) (root 9) 2 2) DegreeOneMiddleResidualSpectrum760.graph sourceMap0401=true := by decide +kernel
theorem fusedMap0401_checked : acceptsGraphIso
    (fused (graph core0401) (root 9) 2 2) DegreeTwoThreeSpectrum4236.graph fusedMap0401=true := by decide +kernel
theorem certified0401 : Certified (graph core0401) (root 9) 2 2 :=
  of_native_maps core0401 DegreeOneMiddleResidualSpectrum760.graph DegreeTwoThreeSpectrum4236.graph
    sourceMap0401 fusedMap0401 sourceMap0401_checked fusedMap0401_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0401
#print axioms sourceMap0401_checked
#print axioms fusedMap0401_checked
#print axioms certified0401
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

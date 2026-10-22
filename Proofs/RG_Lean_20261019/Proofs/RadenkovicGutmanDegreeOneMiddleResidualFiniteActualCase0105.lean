/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0105 : Family 8 := level8.get ⟨62,by decide⟩
def sourceMap0105 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0105 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0105_checked : acceptsGraphIso
    (source (graph core0105) (root 8) 2 2) DegreeOneMiddleResidualSpectrum320.graph sourceMap0105=true := by decide +kernel
theorem fusedMap0105_checked : acceptsGraphIso
    (fused (graph core0105) (root 8) 2 2) DegreeTwoThreeSpectrum2361.graph fusedMap0105=true := by decide +kernel
theorem certified0105 : Certified (graph core0105) (root 8) 2 2 :=
  of_native_maps core0105 DegreeOneMiddleResidualSpectrum320.graph DegreeTwoThreeSpectrum2361.graph
    sourceMap0105 fusedMap0105 sourceMap0105_checked fusedMap0105_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0105
#print axioms sourceMap0105_checked
#print axioms fusedMap0105_checked
#print axioms certified0105
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

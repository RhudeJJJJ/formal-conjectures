/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0622 : Family 10 := level10.get ⟨190,by decide⟩
def sourceMap0622 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0622 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0622_checked : acceptsGraphIso
    (source (graph core0622) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1535.graph sourceMap0622=true := by decide +kernel
theorem fusedMap0622_checked : acceptsGraphIso
    (fused (graph core0622) (root 10) 2 2) DegreeTwoThreeSpectrum5144.graph fusedMap0622=true := by decide +kernel
theorem certified0622 : Certified (graph core0622) (root 10) 2 2 :=
  of_native_maps core0622 DegreeOneMiddleResidualSpectrum1535.graph DegreeTwoThreeSpectrum5144.graph
    sourceMap0622 fusedMap0622 sourceMap0622_checked fusedMap0622_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0622
#print axioms sourceMap0622_checked
#print axioms fusedMap0622_checked
#print axioms certified0622
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

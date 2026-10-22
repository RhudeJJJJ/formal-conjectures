/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0484 : Family 10 := level10.get ⟨0,by decide⟩
def sourceMap0484 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,10,11,12,13,14,15,16,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0484 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (fusedLabel 10 2 2 v)
theorem sourceMap0484_checked : acceptsGraphIso
    (source (graph core0484) (root 10) 2 2) DegreeTwoThreeSpectrum5048.graph sourceMap0484=true := by decide +kernel
theorem fusedMap0484_checked : acceptsGraphIso
    (fused (graph core0484) (root 10) 2 2) DegreeOneMiddleResidualSpectrum935.graph fusedMap0484=true := by decide +kernel
theorem certified0484 : Certified (graph core0484) (root 10) 2 2 :=
  of_native_maps core0484 DegreeTwoThreeSpectrum5048.graph DegreeOneMiddleResidualSpectrum935.graph
    sourceMap0484 fusedMap0484 sourceMap0484_checked fusedMap0484_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0484
#print axioms sourceMap0484_checked
#print axioms fusedMap0484_checked
#print axioms certified0484
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0974 : Family 10 := level10.get ⟨835,by decide⟩
def sourceMap0974 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0974 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0974_checked : acceptsGraphIso
    (source (graph core0974) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2266.graph sourceMap0974=true := by decide +kernel
theorem fusedMap0974_checked : acceptsGraphIso
    (fused (graph core0974) (root 10) 2 2) DegreeTwoThreeSpectrum5663.graph fusedMap0974=true := by decide +kernel
theorem certified0974 : Certified (graph core0974) (root 10) 2 2 :=
  of_native_maps core0974 DegreeOneMiddleResidualSpectrum2266.graph DegreeTwoThreeSpectrum5663.graph
    sourceMap0974 fusedMap0974 sourceMap0974_checked fusedMap0974_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0974
#print axioms sourceMap0974_checked
#print axioms fusedMap0974_checked
#print axioms certified0974
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

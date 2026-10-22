/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0923 : Family 10 := level10.get ⟨726,by decide⟩
def sourceMap0923 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0923 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0923_checked : acceptsGraphIso
    (source (graph core0923) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2190.graph sourceMap0923=true := by decide +kernel
theorem fusedMap0923_checked : acceptsGraphIso
    (fused (graph core0923) (root 10) 2 2) DegreeTwoThreeSpectrum5482.graph fusedMap0923=true := by decide +kernel
theorem certified0923 : Certified (graph core0923) (root 10) 2 2 :=
  of_native_maps core0923 DegreeOneMiddleResidualSpectrum2190.graph DegreeTwoThreeSpectrum5482.graph
    sourceMap0923 fusedMap0923 sourceMap0923_checked fusedMap0923_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0923
#print axioms sourceMap0923_checked
#print axioms fusedMap0923_checked
#print axioms certified0923
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

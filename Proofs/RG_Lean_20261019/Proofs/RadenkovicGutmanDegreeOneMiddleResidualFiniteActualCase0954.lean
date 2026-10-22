/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0954 : Family 10 := level10.get ⟨781,by decide⟩
def sourceMap0954 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0954 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0954_checked : acceptsGraphIso
    (source (graph core0954) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2242.graph sourceMap0954=true := by decide +kernel
theorem fusedMap0954_checked : acceptsGraphIso
    (fused (graph core0954) (root 10) 2 2) DegreeTwoThreeSpectrum5562.graph fusedMap0954=true := by decide +kernel
theorem certified0954 : Certified (graph core0954) (root 10) 2 2 :=
  of_native_maps core0954 DegreeOneMiddleResidualSpectrum2242.graph DegreeTwoThreeSpectrum5562.graph
    sourceMap0954 fusedMap0954 sourceMap0954_checked fusedMap0954_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0954
#print axioms sourceMap0954_checked
#print axioms fusedMap0954_checked
#print axioms certified0954
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

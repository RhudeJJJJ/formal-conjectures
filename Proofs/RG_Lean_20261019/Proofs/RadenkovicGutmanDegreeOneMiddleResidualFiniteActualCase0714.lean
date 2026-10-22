/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0714 : Family 10 := level10.get ⟨327,by decide⟩
def sourceMap0714 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0714 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0714_checked : acceptsGraphIso
    (source (graph core0714) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1796.graph sourceMap0714=true := by decide +kernel
theorem fusedMap0714_checked : acceptsGraphIso
    (fused (graph core0714) (root 10) 2 2) DegreeTwoThreeSpectrum5559.graph fusedMap0714=true := by decide +kernel
theorem certified0714 : Certified (graph core0714) (root 10) 2 2 :=
  of_native_maps core0714 DegreeOneMiddleResidualSpectrum1796.graph DegreeTwoThreeSpectrum5559.graph
    sourceMap0714 fusedMap0714 sourceMap0714_checked fusedMap0714_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0714
#print axioms sourceMap0714_checked
#print axioms fusedMap0714_checked
#print axioms certified0714
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

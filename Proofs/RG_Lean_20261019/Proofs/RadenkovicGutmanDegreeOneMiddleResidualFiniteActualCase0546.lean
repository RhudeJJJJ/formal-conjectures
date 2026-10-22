/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0546 : Family 10 := level10.get ⟨75,by decide⟩
def sourceMap0546 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0546 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0546_checked : acceptsGraphIso
    (source (graph core0546) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1697.graph sourceMap0546=true := by decide +kernel
theorem fusedMap0546_checked : acceptsGraphIso
    (fused (graph core0546) (root 10) 2 2) DegreeTwoThreeSpectrum4990.graph fusedMap0546=true := by decide +kernel
theorem certified0546 : Certified (graph core0546) (root 10) 2 2 :=
  of_native_maps core0546 DegreeOneMiddleResidualSpectrum1697.graph DegreeTwoThreeSpectrum4990.graph
    sourceMap0546 fusedMap0546 sourceMap0546_checked fusedMap0546_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0546
#print axioms sourceMap0546_checked
#print axioms fusedMap0546_checked
#print axioms certified0546
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

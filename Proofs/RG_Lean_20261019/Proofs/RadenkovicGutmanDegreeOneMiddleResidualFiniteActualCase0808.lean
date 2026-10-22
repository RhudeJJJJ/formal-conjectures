/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0808 : Family 10 := level10.get ⟨505,by decide⟩
def sourceMap0808 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0808 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0808_checked : acceptsGraphIso
    (source (graph core0808) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1979.graph sourceMap0808=true := by decide +kernel
theorem fusedMap0808_checked : acceptsGraphIso
    (fused (graph core0808) (root 10) 2 2) DegreeTwoThreeSpectrum5142.graph fusedMap0808=true := by decide +kernel
theorem certified0808 : Certified (graph core0808) (root 10) 2 2 :=
  of_native_maps core0808 DegreeOneMiddleResidualSpectrum1979.graph DegreeTwoThreeSpectrum5142.graph
    sourceMap0808 fusedMap0808 sourceMap0808_checked fusedMap0808_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0808
#print axioms sourceMap0808_checked
#print axioms fusedMap0808_checked
#print axioms certified0808
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0808 : Family 10 := level10.get ⟨1225,by decide⟩
def sourceMap0808 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0808 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0808_checked : acceptsGraphIso
    (source (graph core0808) (root 10) 0 0) DegreeOneSmallSpectrum1046.graph sourceMap0808=true := by decide +kernel
theorem fusedMap0808_checked : acceptsGraphIso
    (fused (graph core0808) (root 10) 0 0) DegreeOneSmallSpectrum1041.graph fusedMap0808=true := by decide +kernel
theorem certified0808 : Certified (graph core0808) (root 10) 0 0 :=
  of_native_maps core0808 DegreeOneSmallSpectrum1046.graph DegreeOneSmallSpectrum1041.graph
    sourceMap0808 fusedMap0808 sourceMap0808_checked fusedMap0808_checked
    DegreeTwoThreeFiniteComparisons.comparison0808
#print axioms sourceMap0808_checked
#print axioms fusedMap0808_checked
#print axioms certified0808
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0808 : Family 8 := level8.get ⟨21,by decide⟩
def sourceMap0808 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0808 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0808_checked : acceptsGraphIso
    (source (graph core0808) (root 8) 0 1) DegreeOneSmallSpectrum557.graph sourceMap0808=true := by decide +kernel
theorem fusedMap0808_checked : acceptsGraphIso
    (fused (graph core0808) (root 8) 0 1) DegreeOneSmallSpectrum388.graph fusedMap0808=true := by decide +kernel
theorem certified0808 : Certified (graph core0808) (root 8) 0 1 :=
  of_native_maps core0808 DegreeOneSmallSpectrum557.graph DegreeOneSmallSpectrum388.graph
    sourceMap0808 fusedMap0808 sourceMap0808_checked fusedMap0808_checked
    DegreeOneSmallComparisons.comparison0808
#print axioms sourceMap0808_checked
#print axioms fusedMap0808_checked
#print axioms certified0808
def sourceMap0808swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0808swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0808swap_checked : acceptsGraphIso
    (source (graph core0808) (root 8) 1 0) DegreeOneSmallSpectrum557.graph sourceMap0808swap=true := by decide +kernel
theorem fusedMap0808swap_checked : acceptsGraphIso
    (fused (graph core0808) (root 8) 1 0) DegreeOneSmallSpectrum388.graph fusedMap0808swap=true := by decide +kernel
theorem certified0808swap : Certified (graph core0808) (root 8) 1 0 :=
  of_native_maps core0808 DegreeOneSmallSpectrum557.graph DegreeOneSmallSpectrum388.graph
    sourceMap0808swap fusedMap0808swap sourceMap0808swap_checked fusedMap0808swap_checked
    DegreeOneSmallComparisons.comparison0808
#print axioms sourceMap0808swap_checked
#print axioms fusedMap0808swap_checked
#print axioms certified0808swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

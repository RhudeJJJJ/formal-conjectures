/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0906 : Family 10 := level10.get ⟨1460,by decide⟩
def sourceMap0906 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0906 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0906_checked : acceptsGraphIso
    (source (graph core0906) (root 10) 0 0) DegreeOneSmallSpectrum1955.graph sourceMap0906=true := by decide +kernel
theorem fusedMap0906_checked : acceptsGraphIso
    (fused (graph core0906) (root 10) 0 0) DegreeOneSmallSpectrum1931.graph fusedMap0906=true := by decide +kernel
theorem certified0906 : Certified (graph core0906) (root 10) 0 0 :=
  of_native_maps core0906 DegreeOneSmallSpectrum1955.graph DegreeOneSmallSpectrum1931.graph
    sourceMap0906 fusedMap0906 sourceMap0906_checked fusedMap0906_checked
    DegreeTwoThreeFiniteComparisons.comparison0906
#print axioms sourceMap0906_checked
#print axioms fusedMap0906_checked
#print axioms certified0906
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

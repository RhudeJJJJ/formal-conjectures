/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0894 : Family 10 := level10.get ⟨1433,by decide⟩
def sourceMap0894 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0894 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0894_checked : acceptsGraphIso
    (source (graph core0894) (root 10) 0 0) DegreeOneSmallSpectrum1808.graph sourceMap0894=true := by decide +kernel
theorem fusedMap0894_checked : acceptsGraphIso
    (fused (graph core0894) (root 10) 0 0) DegreeOneSmallSpectrum1771.graph fusedMap0894=true := by decide +kernel
theorem certified0894 : Certified (graph core0894) (root 10) 0 0 :=
  of_native_maps core0894 DegreeOneSmallSpectrum1808.graph DegreeOneSmallSpectrum1771.graph
    sourceMap0894 fusedMap0894 sourceMap0894_checked fusedMap0894_checked
    DegreeTwoThreeFiniteComparisons.comparison0894
#print axioms sourceMap0894_checked
#print axioms fusedMap0894_checked
#print axioms certified0894
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

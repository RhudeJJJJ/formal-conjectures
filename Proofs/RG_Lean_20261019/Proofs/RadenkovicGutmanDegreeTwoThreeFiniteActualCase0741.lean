/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0741 : Family 10 := level10.get ⟨1068,by decide⟩
def sourceMap0741 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0741 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0741_checked : acceptsGraphIso
    (source (graph core0741) (root 10) 0 0) DegreeOneSmallSpectrum1692.graph sourceMap0741=true := by decide +kernel
theorem fusedMap0741_checked : acceptsGraphIso
    (fused (graph core0741) (root 10) 0 0) DegreeOneSmallSpectrum1687.graph fusedMap0741=true := by decide +kernel
theorem certified0741 : Certified (graph core0741) (root 10) 0 0 :=
  of_native_maps core0741 DegreeOneSmallSpectrum1692.graph DegreeOneSmallSpectrum1687.graph
    sourceMap0741 fusedMap0741 sourceMap0741_checked fusedMap0741_checked
    DegreeTwoThreeFiniteComparisons.comparison0741
#print axioms sourceMap0741_checked
#print axioms fusedMap0741_checked
#print axioms certified0741
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

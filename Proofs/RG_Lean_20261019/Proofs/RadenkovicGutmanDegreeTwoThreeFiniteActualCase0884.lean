/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0884 : Family 10 := level10.get ⟨1411,by decide⟩
def sourceMap0884 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0884 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0884_checked : acceptsGraphIso
    (source (graph core0884) (root 10) 0 0) DegreeOneSmallSpectrum1950.graph sourceMap0884=true := by decide +kernel
theorem fusedMap0884_checked : acceptsGraphIso
    (fused (graph core0884) (root 10) 0 0) DegreeOneSmallSpectrum1926.graph fusedMap0884=true := by decide +kernel
theorem certified0884 : Certified (graph core0884) (root 10) 0 0 :=
  of_native_maps core0884 DegreeOneSmallSpectrum1950.graph DegreeOneSmallSpectrum1926.graph
    sourceMap0884 fusedMap0884 sourceMap0884_checked fusedMap0884_checked
    DegreeTwoThreeFiniteComparisons.comparison0884
#print axioms sourceMap0884_checked
#print axioms fusedMap0884_checked
#print axioms certified0884
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

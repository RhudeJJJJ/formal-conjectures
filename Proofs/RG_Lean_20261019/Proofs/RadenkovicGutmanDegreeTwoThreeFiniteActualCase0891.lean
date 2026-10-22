/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0891 : Family 10 := level10.get ⟨1429,by decide⟩
def sourceMap0891 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,5,6,7,8,9,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0891 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0891_checked : acceptsGraphIso
    (source (graph core0891) (root 10) 0 0) DegreeOneSmallSpectrum1606.graph sourceMap0891=true := by decide +kernel
theorem fusedMap0891_checked : acceptsGraphIso
    (fused (graph core0891) (root 10) 0 0) DegreeOneSmallSpectrum1968.graph fusedMap0891=true := by decide +kernel
theorem certified0891 : Certified (graph core0891) (root 10) 0 0 :=
  of_native_maps core0891 DegreeOneSmallSpectrum1606.graph DegreeOneSmallSpectrum1968.graph
    sourceMap0891 fusedMap0891 sourceMap0891_checked fusedMap0891_checked
    DegreeTwoThreeFiniteComparisons.comparison0891
#print axioms sourceMap0891_checked
#print axioms fusedMap0891_checked
#print axioms certified0891
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

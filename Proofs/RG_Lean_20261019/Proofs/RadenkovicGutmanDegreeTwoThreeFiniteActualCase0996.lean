/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0996 : Family 10 := level10.get ⟨1706,by decide⟩
def sourceMap0996 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0996 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0996_checked : acceptsGraphIso
    (source (graph core0996) (root 10) 0 0) DegreeOneSmallSpectrum1798.graph sourceMap0996=true := by decide +kernel
theorem fusedMap0996_checked : acceptsGraphIso
    (fused (graph core0996) (root 10) 0 0) DegreeOneSmallSpectrum1761.graph fusedMap0996=true := by decide +kernel
theorem certified0996 : Certified (graph core0996) (root 10) 0 0 :=
  of_native_maps core0996 DegreeOneSmallSpectrum1798.graph DegreeOneSmallSpectrum1761.graph
    sourceMap0996 fusedMap0996 sourceMap0996_checked fusedMap0996_checked
    DegreeTwoThreeFiniteComparisons.comparison0996
#print axioms sourceMap0996_checked
#print axioms fusedMap0996_checked
#print axioms certified0996
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0784 : Family 10 := level10.get ⟨1170,by decide⟩
def sourceMap0784 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0784 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0784_checked : acceptsGraphIso
    (source (graph core0784) (root 10) 0 0) DegreeOneSmallSpectrum1649.graph sourceMap0784=true := by decide +kernel
theorem fusedMap0784_checked : acceptsGraphIso
    (fused (graph core0784) (root 10) 0 0) DegreeOneSmallSpectrum1632.graph fusedMap0784=true := by decide +kernel
theorem certified0784 : Certified (graph core0784) (root 10) 0 0 :=
  of_native_maps core0784 DegreeOneSmallSpectrum1649.graph DegreeOneSmallSpectrum1632.graph
    sourceMap0784 fusedMap0784 sourceMap0784_checked fusedMap0784_checked
    DegreeTwoThreeFiniteComparisons.comparison0784
#print axioms sourceMap0784_checked
#print axioms fusedMap0784_checked
#print axioms certified0784
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

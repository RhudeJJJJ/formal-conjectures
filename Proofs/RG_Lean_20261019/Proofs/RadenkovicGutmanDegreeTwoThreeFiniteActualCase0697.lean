/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0697 : Family 10 := level10.get ⟨954,by decide⟩
def sourceMap0697 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0697 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0697_checked : acceptsGraphIso
    (source (graph core0697) (root 10) 0 0) DegreeOneSmallSpectrum1500.graph sourceMap0697=true := by decide +kernel
theorem fusedMap0697_checked : acceptsGraphIso
    (fused (graph core0697) (root 10) 0 0) DegreeOneSmallSpectrum1490.graph fusedMap0697=true := by decide +kernel
theorem certified0697 : Certified (graph core0697) (root 10) 0 0 :=
  of_native_maps core0697 DegreeOneSmallSpectrum1500.graph DegreeOneSmallSpectrum1490.graph
    sourceMap0697 fusedMap0697 sourceMap0697_checked fusedMap0697_checked
    DegreeTwoThreeFiniteComparisons.comparison0697
#print axioms sourceMap0697_checked
#print axioms fusedMap0697_checked
#print axioms certified0697
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

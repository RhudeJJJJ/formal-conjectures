/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0648 : Family 10 := level10.get ⟨823,by decide⟩
def sourceMap0648 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0648 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0648_checked : acceptsGraphIso
    (source (graph core0648) (root 10) 0 0) DegreeOneSmallSpectrum1420.graph sourceMap0648=true := by decide +kernel
theorem fusedMap0648_checked : acceptsGraphIso
    (fused (graph core0648) (root 10) 0 0) DegreeOneSmallSpectrum1410.graph fusedMap0648=true := by decide +kernel
theorem certified0648 : Certified (graph core0648) (root 10) 0 0 :=
  of_native_maps core0648 DegreeOneSmallSpectrum1420.graph DegreeOneSmallSpectrum1410.graph
    sourceMap0648 fusedMap0648 sourceMap0648_checked fusedMap0648_checked
    DegreeTwoThreeFiniteComparisons.comparison0648
#print axioms sourceMap0648_checked
#print axioms fusedMap0648_checked
#print axioms certified0648
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0534 : Family 10 := level10.get ⟨490,by decide⟩
def sourceMap0534 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0534 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0534_checked : acceptsGraphIso
    (source (graph core0534) (root 10) 0 0) DegreeOneSmallSpectrum924.graph sourceMap0534=true := by decide +kernel
theorem fusedMap0534_checked : acceptsGraphIso
    (fused (graph core0534) (root 10) 0 0) DegreeOneSmallSpectrum923.graph fusedMap0534=true := by decide +kernel
theorem certified0534 : Certified (graph core0534) (root 10) 0 0 :=
  of_native_maps core0534 DegreeOneSmallSpectrum924.graph DegreeOneSmallSpectrum923.graph
    sourceMap0534 fusedMap0534 sourceMap0534_checked fusedMap0534_checked
    DegreeTwoThreeFiniteComparisons.comparison0534
#print axioms sourceMap0534_checked
#print axioms fusedMap0534_checked
#print axioms certified0534
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

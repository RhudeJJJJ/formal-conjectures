/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0353 : Family 9 := level9.get ⟨566,by decide⟩
def sourceMap0353 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0353 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0353_checked : acceptsGraphIso
    (source (graph core0353) (root 9) 0 0) DegreeTwoThreeSpectrum713.graph sourceMap0353=true := by decide +kernel
theorem fusedMap0353_checked : acceptsGraphIso
    (fused (graph core0353) (root 9) 0 0) DegreeOneSmallSpectrum634.graph fusedMap0353=true := by decide +kernel
theorem certified0353 : Certified (graph core0353) (root 9) 0 0 :=
  of_native_maps core0353 DegreeTwoThreeSpectrum713.graph DegreeOneSmallSpectrum634.graph
    sourceMap0353 fusedMap0353 sourceMap0353_checked fusedMap0353_checked
    DegreeTwoThreeFiniteComparisons.comparison0353
#print axioms sourceMap0353_checked
#print axioms fusedMap0353_checked
#print axioms certified0353
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

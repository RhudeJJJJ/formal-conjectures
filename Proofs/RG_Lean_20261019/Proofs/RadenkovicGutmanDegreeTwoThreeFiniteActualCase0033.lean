/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0033 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap0033 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0033 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0033_checked : acceptsGraphIso
    (source (graph core0033) (root 7) 0 0) DegreeTwoThreeSpectrum095.graph sourceMap0033=true := by decide +kernel
theorem fusedMap0033_checked : acceptsGraphIso
    (fused (graph core0033) (root 7) 0 0) DegreeOneSmallSpectrum105.graph fusedMap0033=true := by decide +kernel
theorem certified0033 : Certified (graph core0033) (root 7) 0 0 :=
  of_native_maps core0033 DegreeTwoThreeSpectrum095.graph DegreeOneSmallSpectrum105.graph
    sourceMap0033 fusedMap0033 sourceMap0033_checked fusedMap0033_checked
    DegreeTwoThreeFiniteComparisons.comparison0033
#print axioms sourceMap0033_checked
#print axioms fusedMap0033_checked
#print axioms certified0033
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

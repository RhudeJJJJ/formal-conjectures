/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0035 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap0035 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,5,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0035 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,9,8,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap0035_checked : acceptsGraphIso
    (source (graph core0035) (root 7) 0 0) DegreeOneSmallSpectrum099.graph sourceMap0035=true := by decide +kernel
theorem fusedMap0035_checked : acceptsGraphIso
    (fused (graph core0035) (root 7) 0 0) DegreeOneSmallSpectrum127.graph fusedMap0035=true := by decide +kernel
theorem certified0035 : Certified (graph core0035) (root 7) 0 0 :=
  of_native_maps core0035 DegreeOneSmallSpectrum099.graph DegreeOneSmallSpectrum127.graph
    sourceMap0035 fusedMap0035 sourceMap0035_checked fusedMap0035_checked
    DegreeTwoThreeFiniteComparisons.comparison0035
#print axioms sourceMap0035_checked
#print axioms fusedMap0035_checked
#print axioms certified0035
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

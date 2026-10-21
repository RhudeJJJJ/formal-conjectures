/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0519 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0519 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0519 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0519_checked : acceptsGraphIso
    (source (graph core0519) (root 7) 0 0) DegreeOneSmallSpectrum127.graph sourceMap0519=true := by decide +kernel
theorem fusedMap0519_checked : acceptsGraphIso
    (fused (graph core0519) (root 7) 0 0) DegreeOneSmallSpectrum083.graph fusedMap0519=true := by decide +kernel
theorem certified0519 : Certified (graph core0519) (root 7) 0 0 :=
  of_native_maps core0519 DegreeOneSmallSpectrum127.graph DegreeOneSmallSpectrum083.graph
    sourceMap0519 fusedMap0519 sourceMap0519_checked fusedMap0519_checked
    DegreeOneSmallComparisons.comparison0519
#print axioms sourceMap0519_checked
#print axioms fusedMap0519_checked
#print axioms certified0519
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

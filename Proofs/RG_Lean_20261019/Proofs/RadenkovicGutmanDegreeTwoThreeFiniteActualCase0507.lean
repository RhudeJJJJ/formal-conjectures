/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0507 : Family 10 := level10.get ⟨421,by decide⟩
def sourceMap0507 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0507 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0507_checked : acceptsGraphIso
    (source (graph core0507) (root 10) 0 0) DegreeOneSmallSpectrum1020.graph sourceMap0507=true := by decide +kernel
theorem fusedMap0507_checked : acceptsGraphIso
    (fused (graph core0507) (root 10) 0 0) DegreeOneSmallSpectrum1423.graph fusedMap0507=true := by decide +kernel
theorem certified0507 : Certified (graph core0507) (root 10) 0 0 :=
  of_native_maps core0507 DegreeOneSmallSpectrum1020.graph DegreeOneSmallSpectrum1423.graph
    sourceMap0507 fusedMap0507 sourceMap0507_checked fusedMap0507_checked
    DegreeTwoThreeFiniteComparisons.comparison0507
#print axioms sourceMap0507_checked
#print axioms fusedMap0507_checked
#print axioms certified0507
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

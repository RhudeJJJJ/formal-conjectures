/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0762 : Family 8 := level8.get ⟨6,by decide⟩
def sourceMap0762 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0762 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 1 1 v)
theorem sourceMap0762_checked : acceptsGraphIso
    (source (graph core0762) (root 8) 1 1) DegreeOneSmallSpectrum910.graph sourceMap0762=true := by decide +kernel
theorem fusedMap0762_checked : acceptsGraphIso
    (fused (graph core0762) (root 8) 1 1) DegreeOneSmallSpectrum860.graph fusedMap0762=true := by decide +kernel
theorem certified0762 : Certified (graph core0762) (root 8) 1 1 :=
  of_native_maps core0762 DegreeOneSmallSpectrum910.graph DegreeOneSmallSpectrum860.graph
    sourceMap0762 fusedMap0762 sourceMap0762_checked fusedMap0762_checked
    DegreeOneSmallComparisons.comparison0762
#print axioms sourceMap0762_checked
#print axioms fusedMap0762_checked
#print axioms certified0762
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

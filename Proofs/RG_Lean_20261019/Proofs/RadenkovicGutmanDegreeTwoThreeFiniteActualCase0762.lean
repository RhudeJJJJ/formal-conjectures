/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0762 : Family 10 := level10.get ⟨1120,by decide⟩
def sourceMap0762 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0762 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0762_checked : acceptsGraphIso
    (source (graph core0762) (root 10) 0 0) DegreeOneSmallSpectrum1767.graph sourceMap0762=true := by decide +kernel
theorem fusedMap0762_checked : acceptsGraphIso
    (fused (graph core0762) (root 10) 0 0) DegreeOneSmallSpectrum1764.graph fusedMap0762=true := by decide +kernel
theorem certified0762 : Certified (graph core0762) (root 10) 0 0 :=
  of_native_maps core0762 DegreeOneSmallSpectrum1767.graph DegreeOneSmallSpectrum1764.graph
    sourceMap0762 fusedMap0762 sourceMap0762_checked fusedMap0762_checked
    DegreeTwoThreeFiniteComparisons.comparison0762
#print axioms sourceMap0762_checked
#print axioms fusedMap0762_checked
#print axioms certified0762
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

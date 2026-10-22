/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0739 : Family 10 := level10.get ⟨1061,by decide⟩
def sourceMap0739 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0739 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0739_checked : acceptsGraphIso
    (source (graph core0739) (root 10) 0 0) DegreeOneSmallSpectrum1035.graph sourceMap0739=true := by decide +kernel
theorem fusedMap0739_checked : acceptsGraphIso
    (fused (graph core0739) (root 10) 0 0) DegreeOneSmallSpectrum1034.graph fusedMap0739=true := by decide +kernel
theorem certified0739 : Certified (graph core0739) (root 10) 0 0 :=
  of_native_maps core0739 DegreeOneSmallSpectrum1035.graph DegreeOneSmallSpectrum1034.graph
    sourceMap0739 fusedMap0739 sourceMap0739_checked fusedMap0739_checked
    DegreeTwoThreeFiniteComparisons.comparison0739
#print axioms sourceMap0739_checked
#print axioms fusedMap0739_checked
#print axioms certified0739
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

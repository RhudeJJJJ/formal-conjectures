/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0897 : Family 10 := level10.get ⟨1442,by decide⟩
def sourceMap0897 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,5,6,7,8,9,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0897 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0897_checked : acceptsGraphIso
    (source (graph core0897) (root 10) 0 0) DegreeOneSmallSpectrum1621.graph sourceMap0897=true := by decide +kernel
theorem fusedMap0897_checked : acceptsGraphIso
    (fused (graph core0897) (root 10) 0 0) DegreeOneSmallSpectrum1970.graph fusedMap0897=true := by decide +kernel
theorem certified0897 : Certified (graph core0897) (root 10) 0 0 :=
  of_native_maps core0897 DegreeOneSmallSpectrum1621.graph DegreeOneSmallSpectrum1970.graph
    sourceMap0897 fusedMap0897 sourceMap0897_checked fusedMap0897_checked
    DegreeTwoThreeFiniteComparisons.comparison0897
#print axioms sourceMap0897_checked
#print axioms fusedMap0897_checked
#print axioms certified0897
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

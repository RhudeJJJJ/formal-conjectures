/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0950 : Family 10 := level10.get ⟨1579,by decide⟩
def sourceMap0950 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0950 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0950_checked : acceptsGraphIso
    (source (graph core0950) (root 10) 0 0) DegreeOneSmallSpectrum1637.graph sourceMap0950=true := by decide +kernel
theorem fusedMap0950_checked : acceptsGraphIso
    (fused (graph core0950) (root 10) 0 0) DegreeOneSmallSpectrum1636.graph fusedMap0950=true := by decide +kernel
theorem certified0950 : Certified (graph core0950) (root 10) 0 0 :=
  of_native_maps core0950 DegreeOneSmallSpectrum1637.graph DegreeOneSmallSpectrum1636.graph
    sourceMap0950 fusedMap0950 sourceMap0950_checked fusedMap0950_checked
    DegreeTwoThreeFiniteComparisons.comparison0950
#print axioms sourceMap0950_checked
#print axioms fusedMap0950_checked
#print axioms certified0950
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

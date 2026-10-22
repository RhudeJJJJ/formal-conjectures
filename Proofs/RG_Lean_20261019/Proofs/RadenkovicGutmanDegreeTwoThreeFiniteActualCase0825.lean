/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0825 : Family 10 := level10.get ⟨1274,by decide⟩
def sourceMap0825 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0825 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0825_checked : acceptsGraphIso
    (source (graph core0825) (root 10) 0 0) DegreeOneSmallSpectrum1613.graph sourceMap0825=true := by decide +kernel
theorem fusedMap0825_checked : acceptsGraphIso
    (fused (graph core0825) (root 10) 0 0) DegreeOneSmallSpectrum1923.graph fusedMap0825=true := by decide +kernel
theorem certified0825 : Certified (graph core0825) (root 10) 0 0 :=
  of_native_maps core0825 DegreeOneSmallSpectrum1613.graph DegreeOneSmallSpectrum1923.graph
    sourceMap0825 fusedMap0825 sourceMap0825_checked fusedMap0825_checked
    DegreeTwoThreeFiniteComparisons.comparison0825
#print axioms sourceMap0825_checked
#print axioms fusedMap0825_checked
#print axioms certified0825
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

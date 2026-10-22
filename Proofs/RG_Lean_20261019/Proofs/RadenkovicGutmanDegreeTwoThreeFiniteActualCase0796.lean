/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0796 : Family 10 := level10.get ⟨1201,by decide⟩
def sourceMap0796 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0796 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0796_checked : acceptsGraphIso
    (source (graph core0796) (root 10) 0 0) DegreeOneSmallSpectrum1796.graph sourceMap0796=true := by decide +kernel
theorem fusedMap0796_checked : acceptsGraphIso
    (fused (graph core0796) (root 10) 0 0) DegreeOneSmallSpectrum1759.graph fusedMap0796=true := by decide +kernel
theorem certified0796 : Certified (graph core0796) (root 10) 0 0 :=
  of_native_maps core0796 DegreeOneSmallSpectrum1796.graph DegreeOneSmallSpectrum1759.graph
    sourceMap0796 fusedMap0796 sourceMap0796_checked fusedMap0796_checked
    DegreeTwoThreeFiniteComparisons.comparison0796
#print axioms sourceMap0796_checked
#print axioms fusedMap0796_checked
#print axioms certified0796
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

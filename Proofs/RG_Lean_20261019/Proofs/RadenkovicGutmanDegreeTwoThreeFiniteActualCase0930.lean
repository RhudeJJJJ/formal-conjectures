/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0930 : Family 10 := level10.get ⟨1535,by decide⟩
def sourceMap0930 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0930 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0930_checked : acceptsGraphIso
    (source (graph core0930) (root 10) 0 0) DegreeTwoThreeSpectrum1689.graph sourceMap0930=true := by decide +kernel
theorem fusedMap0930_checked : acceptsGraphIso
    (fused (graph core0930) (root 10) 0 0) DegreeOneSmallSpectrum1539.graph fusedMap0930=true := by decide +kernel
theorem certified0930 : Certified (graph core0930) (root 10) 0 0 :=
  of_native_maps core0930 DegreeTwoThreeSpectrum1689.graph DegreeOneSmallSpectrum1539.graph
    sourceMap0930 fusedMap0930 sourceMap0930_checked fusedMap0930_checked
    DegreeTwoThreeFiniteComparisons.comparison0930
#print axioms sourceMap0930_checked
#print axioms fusedMap0930_checked
#print axioms certified0930
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

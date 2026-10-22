/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0846 : Family 10 := level10.get ⟨1325,by decide⟩
def sourceMap0846 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0846 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0846_checked : acceptsGraphIso
    (source (graph core0846) (root 10) 0 0) DegreeTwoThreeSpectrum1378.graph sourceMap0846=true := by decide +kernel
theorem fusedMap0846_checked : acceptsGraphIso
    (fused (graph core0846) (root 10) 0 0) DegreeOneSmallSpectrum1948.graph fusedMap0846=true := by decide +kernel
theorem certified0846 : Certified (graph core0846) (root 10) 0 0 :=
  of_native_maps core0846 DegreeTwoThreeSpectrum1378.graph DegreeOneSmallSpectrum1948.graph
    sourceMap0846 fusedMap0846 sourceMap0846_checked fusedMap0846_checked
    DegreeTwoThreeFiniteComparisons.comparison0846
#print axioms sourceMap0846_checked
#print axioms fusedMap0846_checked
#print axioms certified0846
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0740 : Family 10 := level10.get ⟨1062,by decide⟩
def sourceMap0740 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0740 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0740_checked : acceptsGraphIso
    (source (graph core0740) (root 10) 0 0) DegreeOneSmallSpectrum1659.graph sourceMap0740=true := by decide +kernel
theorem fusedMap0740_checked : acceptsGraphIso
    (fused (graph core0740) (root 10) 0 0) DegreeOneSmallSpectrum1657.graph fusedMap0740=true := by decide +kernel
theorem certified0740 : Certified (graph core0740) (root 10) 0 0 :=
  of_native_maps core0740 DegreeOneSmallSpectrum1659.graph DegreeOneSmallSpectrum1657.graph
    sourceMap0740 fusedMap0740 sourceMap0740_checked fusedMap0740_checked
    DegreeTwoThreeFiniteComparisons.comparison0740
#print axioms sourceMap0740_checked
#print axioms fusedMap0740_checked
#print axioms certified0740
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

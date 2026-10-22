/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0668 : Family 10 := level10.get ⟨881,by decide⟩
def sourceMap0668 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0668 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0668_checked : acceptsGraphIso
    (source (graph core0668) (root 10) 0 0) DegreeOneSmallSpectrum1389.graph sourceMap0668=true := by decide +kernel
theorem fusedMap0668_checked : acceptsGraphIso
    (fused (graph core0668) (root 10) 0 0) DegreeOneSmallSpectrum1344.graph fusedMap0668=true := by decide +kernel
theorem certified0668 : Certified (graph core0668) (root 10) 0 0 :=
  of_native_maps core0668 DegreeOneSmallSpectrum1389.graph DegreeOneSmallSpectrum1344.graph
    sourceMap0668 fusedMap0668 sourceMap0668_checked fusedMap0668_checked
    DegreeTwoThreeFiniteComparisons.comparison0668
#print axioms sourceMap0668_checked
#print axioms fusedMap0668_checked
#print axioms certified0668
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

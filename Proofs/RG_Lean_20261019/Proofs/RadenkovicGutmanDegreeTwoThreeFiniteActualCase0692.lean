/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0692 : Family 10 := level10.get ⟨945,by decide⟩
def sourceMap0692 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,6,7,8,9,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0692 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0692_checked : acceptsGraphIso
    (source (graph core0692) (root 10) 0 0) DegreeOneSmallSpectrum1609.graph sourceMap0692=true := by decide +kernel
theorem fusedMap0692_checked : acceptsGraphIso
    (fused (graph core0692) (root 10) 0 0) DegreeOneSmallSpectrum1400.graph fusedMap0692=true := by decide +kernel
theorem certified0692 : Certified (graph core0692) (root 10) 0 0 :=
  of_native_maps core0692 DegreeOneSmallSpectrum1609.graph DegreeOneSmallSpectrum1400.graph
    sourceMap0692 fusedMap0692 sourceMap0692_checked fusedMap0692_checked
    DegreeTwoThreeFiniteComparisons.comparison0692
#print axioms sourceMap0692_checked
#print axioms fusedMap0692_checked
#print axioms certified0692
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

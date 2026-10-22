/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0506 : Family 10 := level10.get ⟨419,by decide⟩
def sourceMap0506 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0506 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0506_checked : acceptsGraphIso
    (source (graph core0506) (root 10) 0 0) DegreeOneSmallSpectrum1014.graph sourceMap0506=true := by decide +kernel
theorem fusedMap0506_checked : acceptsGraphIso
    (fused (graph core0506) (root 10) 0 0) DegreeOneSmallSpectrum1413.graph fusedMap0506=true := by decide +kernel
theorem certified0506 : Certified (graph core0506) (root 10) 0 0 :=
  of_native_maps core0506 DegreeOneSmallSpectrum1014.graph DegreeOneSmallSpectrum1413.graph
    sourceMap0506 fusedMap0506 sourceMap0506_checked fusedMap0506_checked
    DegreeTwoThreeFiniteComparisons.comparison0506
#print axioms sourceMap0506_checked
#print axioms fusedMap0506_checked
#print axioms certified0506
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

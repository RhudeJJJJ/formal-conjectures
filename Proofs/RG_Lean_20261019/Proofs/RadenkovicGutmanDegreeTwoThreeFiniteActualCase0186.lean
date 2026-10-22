/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0186 : Family 9 := level9.get ⟨119,by decide⟩
def sourceMap0186 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0186 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0186_checked : acceptsGraphIso
    (source (graph core0186) (root 9) 0 0) DegreeOneSmallSpectrum413.graph sourceMap0186=true := by decide +kernel
theorem fusedMap0186_checked : acceptsGraphIso
    (fused (graph core0186) (root 9) 0 0) DegreeOneSmallSpectrum560.graph fusedMap0186=true := by decide +kernel
theorem certified0186 : Certified (graph core0186) (root 9) 0 0 :=
  of_native_maps core0186 DegreeOneSmallSpectrum413.graph DegreeOneSmallSpectrum560.graph
    sourceMap0186 fusedMap0186 sourceMap0186_checked fusedMap0186_checked
    DegreeTwoThreeFiniteComparisons.comparison0186
#print axioms sourceMap0186_checked
#print axioms fusedMap0186_checked
#print axioms certified0186
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

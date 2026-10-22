/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0339 : Family 9 := level9.get ⟨527,by decide⟩
def sourceMap0339 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0339 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0339_checked : acceptsGraphIso
    (source (graph core0339) (root 9) 0 0) DegreeOneSmallSpectrum413.graph sourceMap0339=true := by decide +kernel
theorem fusedMap0339_checked : acceptsGraphIso
    (fused (graph core0339) (root 9) 0 0) DegreeOneSmallSpectrum412.graph fusedMap0339=true := by decide +kernel
theorem certified0339 : Certified (graph core0339) (root 9) 0 0 :=
  of_native_maps core0339 DegreeOneSmallSpectrum413.graph DegreeOneSmallSpectrum412.graph
    sourceMap0339 fusedMap0339 sourceMap0339_checked fusedMap0339_checked
    DegreeTwoThreeFiniteComparisons.comparison0339
#print axioms sourceMap0339_checked
#print axioms fusedMap0339_checked
#print axioms certified0339
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

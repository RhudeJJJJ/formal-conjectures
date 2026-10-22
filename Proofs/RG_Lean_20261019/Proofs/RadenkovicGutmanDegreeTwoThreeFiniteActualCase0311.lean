/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0311 : Family 9 := level9.get ⟨466,by decide⟩
def sourceMap0311 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0311 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0311_checked : acceptsGraphIso
    (source (graph core0311) (root 9) 0 0) DegreeOneSmallSpectrum634.graph sourceMap0311=true := by decide +kernel
theorem fusedMap0311_checked : acceptsGraphIso
    (fused (graph core0311) (root 9) 0 0) DegreeOneSmallSpectrum814.graph fusedMap0311=true := by decide +kernel
theorem certified0311 : Certified (graph core0311) (root 9) 0 0 :=
  of_native_maps core0311 DegreeOneSmallSpectrum634.graph DegreeOneSmallSpectrum814.graph
    sourceMap0311 fusedMap0311 sourceMap0311_checked fusedMap0311_checked
    DegreeTwoThreeFiniteComparisons.comparison0311
#print axioms sourceMap0311_checked
#print axioms fusedMap0311_checked
#print axioms certified0311
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

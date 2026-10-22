/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0328 : Family 9 := level9.get ⟨503,by decide⟩
def sourceMap0328 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0328 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0328_checked : acceptsGraphIso
    (source (graph core0328) (root 9) 0 0) DegreeOneSmallSpectrum810.graph sourceMap0328=true := by decide +kernel
theorem fusedMap0328_checked : acceptsGraphIso
    (fused (graph core0328) (root 9) 0 0) DegreeOneSmallSpectrum796.graph fusedMap0328=true := by decide +kernel
theorem certified0328 : Certified (graph core0328) (root 9) 0 0 :=
  of_native_maps core0328 DegreeOneSmallSpectrum810.graph DegreeOneSmallSpectrum796.graph
    sourceMap0328 fusedMap0328 sourceMap0328_checked fusedMap0328_checked
    DegreeTwoThreeFiniteComparisons.comparison0328
#print axioms sourceMap0328_checked
#print axioms fusedMap0328_checked
#print axioms certified0328
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

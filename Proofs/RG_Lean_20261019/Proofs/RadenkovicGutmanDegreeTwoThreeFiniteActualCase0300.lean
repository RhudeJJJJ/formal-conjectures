/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0300 : Family 9 := level9.get ⟨435,by decide⟩
def sourceMap0300 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0300 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0300_checked : acceptsGraphIso
    (source (graph core0300) (root 9) 0 0) DegreeOneSmallSpectrum723.graph sourceMap0300=true := by decide +kernel
theorem fusedMap0300_checked : acceptsGraphIso
    (fused (graph core0300) (root 9) 0 0) DegreeOneSmallSpectrum703.graph fusedMap0300=true := by decide +kernel
theorem certified0300 : Certified (graph core0300) (root 9) 0 0 :=
  of_native_maps core0300 DegreeOneSmallSpectrum723.graph DegreeOneSmallSpectrum703.graph
    sourceMap0300 fusedMap0300 sourceMap0300_checked fusedMap0300_checked
    DegreeTwoThreeFiniteComparisons.comparison0300
#print axioms sourceMap0300_checked
#print axioms fusedMap0300_checked
#print axioms certified0300
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

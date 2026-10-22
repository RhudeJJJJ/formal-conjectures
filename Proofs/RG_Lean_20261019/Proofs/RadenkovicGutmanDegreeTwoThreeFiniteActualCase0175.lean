/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0175 : Family 9 := level9.get ⟨78,by decide⟩
def sourceMap0175 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0175 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0175_checked : acceptsGraphIso
    (source (graph core0175) (root 9) 0 0) DegreeTwoThreeSpectrum370.graph sourceMap0175=true := by decide +kernel
theorem fusedMap0175_checked : acceptsGraphIso
    (fused (graph core0175) (root 9) 0 0) DegreeOneSmallSpectrum530.graph fusedMap0175=true := by decide +kernel
theorem certified0175 : Certified (graph core0175) (root 9) 0 0 :=
  of_native_maps core0175 DegreeTwoThreeSpectrum370.graph DegreeOneSmallSpectrum530.graph
    sourceMap0175 fusedMap0175 sourceMap0175_checked fusedMap0175_checked
    DegreeTwoThreeFiniteComparisons.comparison0175
#print axioms sourceMap0175_checked
#print axioms fusedMap0175_checked
#print axioms certified0175
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

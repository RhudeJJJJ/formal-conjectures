/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0121 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap0121 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0121 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0121_checked : acceptsGraphIso
    (source (graph core0121) (root 8) 0 0) DegreeOneSmallSpectrum291.graph sourceMap0121=true := by decide +kernel
theorem fusedMap0121_checked : acceptsGraphIso
    (fused (graph core0121) (root 8) 0 0) DegreeOneSmallSpectrum281.graph fusedMap0121=true := by decide +kernel
theorem certified0121 : Certified (graph core0121) (root 8) 0 0 :=
  of_native_maps core0121 DegreeOneSmallSpectrum291.graph DegreeOneSmallSpectrum281.graph
    sourceMap0121 fusedMap0121 sourceMap0121_checked fusedMap0121_checked
    DegreeTwoThreeFiniteComparisons.comparison0121
#print axioms sourceMap0121_checked
#print axioms fusedMap0121_checked
#print axioms certified0121
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

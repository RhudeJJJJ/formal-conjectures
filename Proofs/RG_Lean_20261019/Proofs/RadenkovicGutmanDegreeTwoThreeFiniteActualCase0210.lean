/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0210 : Family 9 := level9.get ⟨193,by decide⟩
def sourceMap0210 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,11,7,8,9,10] (sourceLabel 9 0 0 v)
def fusedMap0210 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,11,7,8,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0210_checked : acceptsGraphIso
    (source (graph core0210) (root 9) 0 0) DegreeOneSmallSpectrum485.graph sourceMap0210=true := by decide +kernel
theorem fusedMap0210_checked : acceptsGraphIso
    (fused (graph core0210) (root 9) 0 0) DegreeOneSmallSpectrum482.graph fusedMap0210=true := by decide +kernel
theorem certified0210 : Certified (graph core0210) (root 9) 0 0 :=
  of_native_maps core0210 DegreeOneSmallSpectrum485.graph DegreeOneSmallSpectrum482.graph
    sourceMap0210 fusedMap0210 sourceMap0210_checked fusedMap0210_checked
    DegreeTwoThreeFiniteComparisons.comparison0210
#print axioms sourceMap0210_checked
#print axioms fusedMap0210_checked
#print axioms certified0210
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

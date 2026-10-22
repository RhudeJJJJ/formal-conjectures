/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0228 : Family 9 := level9.get ⟨247,by decide⟩
def sourceMap0228 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0228 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0228_checked : acceptsGraphIso
    (source (graph core0228) (root 9) 0 0) DegreeOneSmallSpectrum557.graph sourceMap0228=true := by decide +kernel
theorem fusedMap0228_checked : acceptsGraphIso
    (fused (graph core0228) (root 9) 0 0) DegreeOneSmallSpectrum555.graph fusedMap0228=true := by decide +kernel
theorem certified0228 : Certified (graph core0228) (root 9) 0 0 :=
  of_native_maps core0228 DegreeOneSmallSpectrum557.graph DegreeOneSmallSpectrum555.graph
    sourceMap0228 fusedMap0228 sourceMap0228_checked fusedMap0228_checked
    DegreeTwoThreeFiniteComparisons.comparison0228
#print axioms sourceMap0228_checked
#print axioms fusedMap0228_checked
#print axioms certified0228
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

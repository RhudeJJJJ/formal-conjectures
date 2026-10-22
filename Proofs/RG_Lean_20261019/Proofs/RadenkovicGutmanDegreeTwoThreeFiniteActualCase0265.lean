/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0265 : Family 9 := level9.get ⟨348,by decide⟩
def sourceMap0265 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 9 0 0 v)
def fusedMap0265 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0265_checked : acceptsGraphIso
    (source (graph core0265) (root 9) 0 0) DegreeTwoThreeSpectrum590.graph sourceMap0265=true := by decide +kernel
theorem fusedMap0265_checked : acceptsGraphIso
    (fused (graph core0265) (root 9) 0 0) DegreeOneSmallSpectrum666.graph fusedMap0265=true := by decide +kernel
theorem certified0265 : Certified (graph core0265) (root 9) 0 0 :=
  of_native_maps core0265 DegreeTwoThreeSpectrum590.graph DegreeOneSmallSpectrum666.graph
    sourceMap0265 fusedMap0265 sourceMap0265_checked fusedMap0265_checked
    DegreeTwoThreeFiniteComparisons.comparison0265
#print axioms sourceMap0265_checked
#print axioms fusedMap0265_checked
#print axioms certified0265
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

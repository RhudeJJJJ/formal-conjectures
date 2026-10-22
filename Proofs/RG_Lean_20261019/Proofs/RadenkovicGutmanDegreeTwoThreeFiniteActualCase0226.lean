/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0226 : Family 9 := level9.get ⟨244,by decide⟩
def sourceMap0226 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0226 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0226_checked : acceptsGraphIso
    (source (graph core0226) (root 9) 0 0) DegreeOneSmallSpectrum648.graph sourceMap0226=true := by decide +kernel
theorem fusedMap0226_checked : acceptsGraphIso
    (fused (graph core0226) (root 9) 0 0) DegreeOneSmallSpectrum542.graph fusedMap0226=true := by decide +kernel
theorem certified0226 : Certified (graph core0226) (root 9) 0 0 :=
  of_native_maps core0226 DegreeOneSmallSpectrum648.graph DegreeOneSmallSpectrum542.graph
    sourceMap0226 fusedMap0226 sourceMap0226_checked fusedMap0226_checked
    DegreeTwoThreeFiniteComparisons.comparison0226
#print axioms sourceMap0226_checked
#print axioms fusedMap0226_checked
#print axioms certified0226
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

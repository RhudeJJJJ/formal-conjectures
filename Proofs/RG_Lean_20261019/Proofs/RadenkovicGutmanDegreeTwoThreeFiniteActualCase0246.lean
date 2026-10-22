/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0246 : Family 9 := level9.get ⟨298,by decide⟩
def sourceMap0246 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,6,7,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0246 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,6,7,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0246_checked : acceptsGraphIso
    (source (graph core0246) (root 9) 0 0) DegreeOneSmallSpectrum524.graph sourceMap0246=true := by decide +kernel
theorem fusedMap0246_checked : acceptsGraphIso
    (fused (graph core0246) (root 9) 0 0) DegreeOneSmallSpectrum506.graph fusedMap0246=true := by decide +kernel
theorem certified0246 : Certified (graph core0246) (root 9) 0 0 :=
  of_native_maps core0246 DegreeOneSmallSpectrum524.graph DegreeOneSmallSpectrum506.graph
    sourceMap0246 fusedMap0246 sourceMap0246_checked fusedMap0246_checked
    DegreeTwoThreeFiniteComparisons.comparison0246
#print axioms sourceMap0246_checked
#print axioms fusedMap0246_checked
#print axioms certified0246
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

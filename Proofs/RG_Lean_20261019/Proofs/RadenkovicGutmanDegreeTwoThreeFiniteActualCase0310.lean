/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0310 : Family 9 := level9.get ⟨463,by decide⟩
def sourceMap0310 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0310 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0310_checked : acceptsGraphIso
    (source (graph core0310) (root 9) 0 0) DegreeOneSmallSpectrum629.graph sourceMap0310=true := by decide +kernel
theorem fusedMap0310_checked : acceptsGraphIso
    (fused (graph core0310) (root 9) 0 0) DegreeOneSmallSpectrum813.graph fusedMap0310=true := by decide +kernel
theorem certified0310 : Certified (graph core0310) (root 9) 0 0 :=
  of_native_maps core0310 DegreeOneSmallSpectrum629.graph DegreeOneSmallSpectrum813.graph
    sourceMap0310 fusedMap0310 sourceMap0310_checked fusedMap0310_checked
    DegreeTwoThreeFiniteComparisons.comparison0310
#print axioms sourceMap0310_checked
#print axioms fusedMap0310_checked
#print axioms certified0310
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0222 : Family 9 := level9.get ⟨233,by decide⟩
def sourceMap0222 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0222 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0222_checked : acceptsGraphIso
    (source (graph core0222) (root 9) 0 0) DegreeOneSmallSpectrum668.graph sourceMap0222=true := by decide +kernel
theorem fusedMap0222_checked : acceptsGraphIso
    (fused (graph core0222) (root 9) 0 0) DegreeOneSmallSpectrum542.graph fusedMap0222=true := by decide +kernel
theorem certified0222 : Certified (graph core0222) (root 9) 0 0 :=
  of_native_maps core0222 DegreeOneSmallSpectrum668.graph DegreeOneSmallSpectrum542.graph
    sourceMap0222 fusedMap0222 sourceMap0222_checked fusedMap0222_checked
    DegreeTwoThreeFiniteComparisons.comparison0222
#print axioms sourceMap0222_checked
#print axioms fusedMap0222_checked
#print axioms certified0222
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

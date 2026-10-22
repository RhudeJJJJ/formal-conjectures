/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0248 : Family 9 := level9.get ⟨302,by decide⟩
def sourceMap0248 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,6,7,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0248 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,6,7,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0248_checked : acceptsGraphIso
    (source (graph core0248) (root 9) 0 0) DegreeOneSmallSpectrum525.graph sourceMap0248=true := by decide +kernel
theorem fusedMap0248_checked : acceptsGraphIso
    (fused (graph core0248) (root 9) 0 0) DegreeOneSmallSpectrum507.graph fusedMap0248=true := by decide +kernel
theorem certified0248 : Certified (graph core0248) (root 9) 0 0 :=
  of_native_maps core0248 DegreeOneSmallSpectrum525.graph DegreeOneSmallSpectrum507.graph
    sourceMap0248 fusedMap0248 sourceMap0248_checked fusedMap0248_checked
    DegreeTwoThreeFiniteComparisons.comparison0248
#print axioms sourceMap0248_checked
#print axioms fusedMap0248_checked
#print axioms certified0248
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

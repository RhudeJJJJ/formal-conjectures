/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0199 : Family 9 := level9.get ⟨160,by decide⟩
def sourceMap0199 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0199 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0199_checked : acceptsGraphIso
    (source (graph core0199) (root 9) 0 0) DegreeOneSmallSpectrum660.graph sourceMap0199=true := by decide +kernel
theorem fusedMap0199_checked : acceptsGraphIso
    (fused (graph core0199) (root 9) 0 0) DegreeOneSmallSpectrum432.graph fusedMap0199=true := by decide +kernel
theorem certified0199 : Certified (graph core0199) (root 9) 0 0 :=
  of_native_maps core0199 DegreeOneSmallSpectrum660.graph DegreeOneSmallSpectrum432.graph
    sourceMap0199 fusedMap0199 sourceMap0199_checked fusedMap0199_checked
    DegreeTwoThreeFiniteComparisons.comparison0199
#print axioms sourceMap0199_checked
#print axioms fusedMap0199_checked
#print axioms certified0199
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

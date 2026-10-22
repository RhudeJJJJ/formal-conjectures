/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0202 : Family 9 := level9.get ⟨171,by decide⟩
def sourceMap0202 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0202 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0202_checked : acceptsGraphIso
    (source (graph core0202) (root 9) 0 0) DegreeOneSmallSpectrum652.graph sourceMap0202=true := by decide +kernel
theorem fusedMap0202_checked : acceptsGraphIso
    (fused (graph core0202) (root 9) 0 0) DegreeOneSmallSpectrum452.graph fusedMap0202=true := by decide +kernel
theorem certified0202 : Certified (graph core0202) (root 9) 0 0 :=
  of_native_maps core0202 DegreeOneSmallSpectrum652.graph DegreeOneSmallSpectrum452.graph
    sourceMap0202 fusedMap0202 sourceMap0202_checked fusedMap0202_checked
    DegreeTwoThreeFiniteComparisons.comparison0202
#print axioms sourceMap0202_checked
#print axioms fusedMap0202_checked
#print axioms certified0202
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

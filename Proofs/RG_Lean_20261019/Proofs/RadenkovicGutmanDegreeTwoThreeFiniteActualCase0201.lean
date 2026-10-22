/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0201 : Family 9 := level9.get ⟨168,by decide⟩
def sourceMap0201 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0201 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0201_checked : acceptsGraphIso
    (source (graph core0201) (root 9) 0 0) DegreeOneSmallSpectrum663.graph sourceMap0201=true := by decide +kernel
theorem fusedMap0201_checked : acceptsGraphIso
    (fused (graph core0201) (root 9) 0 0) DegreeOneSmallSpectrum444.graph fusedMap0201=true := by decide +kernel
theorem certified0201 : Certified (graph core0201) (root 9) 0 0 :=
  of_native_maps core0201 DegreeOneSmallSpectrum663.graph DegreeOneSmallSpectrum444.graph
    sourceMap0201 fusedMap0201 sourceMap0201_checked fusedMap0201_checked
    DegreeTwoThreeFiniteComparisons.comparison0201
#print axioms sourceMap0201_checked
#print axioms fusedMap0201_checked
#print axioms certified0201
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

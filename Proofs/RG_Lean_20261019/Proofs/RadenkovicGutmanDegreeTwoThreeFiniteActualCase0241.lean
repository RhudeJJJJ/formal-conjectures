/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0241 : Family 9 := level9.get ⟨283,by decide⟩
def sourceMap0241 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0241 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0241_checked : acceptsGraphIso
    (source (graph core0241) (root 9) 0 0) DegreeOneSmallSpectrum580.graph sourceMap0241=true := by decide +kernel
theorem fusedMap0241_checked : acceptsGraphIso
    (fused (graph core0241) (root 9) 0 0) DegreeOneSmallSpectrum574.graph fusedMap0241=true := by decide +kernel
theorem certified0241 : Certified (graph core0241) (root 9) 0 0 :=
  of_native_maps core0241 DegreeOneSmallSpectrum580.graph DegreeOneSmallSpectrum574.graph
    sourceMap0241 fusedMap0241 sourceMap0241_checked fusedMap0241_checked
    DegreeTwoThreeFiniteComparisons.comparison0241
#print axioms sourceMap0241_checked
#print axioms fusedMap0241_checked
#print axioms certified0241
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

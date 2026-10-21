/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0201 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0201 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 5 1 1 v)
def fusedMap0201 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0201_checked : acceptsGraphIso
    (source (graph core0201) (root 5) 1 1) DegreeOneSmallSpectrum137.graph sourceMap0201=true := by decide +kernel
theorem fusedMap0201_checked : acceptsGraphIso
    (fused (graph core0201) (root 5) 1 1) DegreeOneSmallSpectrum090.graph fusedMap0201=true := by decide +kernel
theorem certified0201 : Certified (graph core0201) (root 5) 1 1 :=
  of_native_maps core0201 DegreeOneSmallSpectrum137.graph DegreeOneSmallSpectrum090.graph
    sourceMap0201 fusedMap0201 sourceMap0201_checked fusedMap0201_checked
    DegreeOneSmallComparisons.comparison0201
#print axioms sourceMap0201_checked
#print axioms fusedMap0201_checked
#print axioms certified0201
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

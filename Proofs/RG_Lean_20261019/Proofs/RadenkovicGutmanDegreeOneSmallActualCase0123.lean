/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0123 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0123 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 2 2 v)
def fusedMap0123 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap0123_checked : acceptsGraphIso
    (source (graph core0123) (root 4) 2 2) DegreeOneSmallSpectrum312.graph sourceMap0123=true := by decide +kernel
theorem fusedMap0123_checked : acceptsGraphIso
    (fused (graph core0123) (root 4) 2 2) DegreeOneSmallSpectrum164.graph fusedMap0123=true := by decide +kernel
theorem certified0123 : Certified (graph core0123) (root 4) 2 2 :=
  of_native_maps core0123 DegreeOneSmallSpectrum312.graph DegreeOneSmallSpectrum164.graph
    sourceMap0123 fusedMap0123 sourceMap0123_checked fusedMap0123_checked
    DegreeOneSmallComparisons.comparison0123
#print axioms sourceMap0123_checked
#print axioms fusedMap0123_checked
#print axioms certified0123
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

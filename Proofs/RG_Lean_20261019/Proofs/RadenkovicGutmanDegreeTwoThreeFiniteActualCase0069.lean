/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0069 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap0069 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0069 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0069_checked : acceptsGraphIso
    (source (graph core0069) (root 8) 0 0) DegreeOneSmallSpectrum170.graph sourceMap0069=true := by decide +kernel
theorem fusedMap0069_checked : acceptsGraphIso
    (fused (graph core0069) (root 8) 0 0) DegreeOneSmallSpectrum212.graph fusedMap0069=true := by decide +kernel
theorem certified0069 : Certified (graph core0069) (root 8) 0 0 :=
  of_native_maps core0069 DegreeOneSmallSpectrum170.graph DegreeOneSmallSpectrum212.graph
    sourceMap0069 fusedMap0069 sourceMap0069_checked fusedMap0069_checked
    DegreeTwoThreeFiniteComparisons.comparison0069
#print axioms sourceMap0069_checked
#print axioms fusedMap0069_checked
#print axioms certified0069
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0999 : Family 10 := level10.get ⟨1713,by decide⟩
def sourceMap0999 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0999 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0999_checked : acceptsGraphIso
    (source (graph core0999) (root 10) 0 0) DegreeOneSmallSpectrum1907.graph sourceMap0999=true := by decide +kernel
theorem fusedMap0999_checked : acceptsGraphIso
    (fused (graph core0999) (root 10) 0 0) DegreeOneSmallSpectrum1906.graph fusedMap0999=true := by decide +kernel
theorem certified0999 : Certified (graph core0999) (root 10) 0 0 :=
  of_native_maps core0999 DegreeOneSmallSpectrum1907.graph DegreeOneSmallSpectrum1906.graph
    sourceMap0999 fusedMap0999 sourceMap0999_checked fusedMap0999_checked
    DegreeTwoThreeFiniteComparisons.comparison0999
#print axioms sourceMap0999_checked
#print axioms fusedMap0999_checked
#print axioms certified0999
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

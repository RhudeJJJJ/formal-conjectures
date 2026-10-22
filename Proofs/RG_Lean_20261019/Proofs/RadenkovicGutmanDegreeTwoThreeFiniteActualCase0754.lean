/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0754 : Family 10 := level10.get ⟨1100,by decide⟩
def sourceMap0754 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0754 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0754_checked : acceptsGraphIso
    (source (graph core0754) (root 10) 0 0) DegreeOneSmallSpectrum1655.graph sourceMap0754=true := by decide +kernel
theorem fusedMap0754_checked : acceptsGraphIso
    (fused (graph core0754) (root 10) 0 0) DegreeOneSmallSpectrum1720.graph fusedMap0754=true := by decide +kernel
theorem certified0754 : Certified (graph core0754) (root 10) 0 0 :=
  of_native_maps core0754 DegreeOneSmallSpectrum1655.graph DegreeOneSmallSpectrum1720.graph
    sourceMap0754 fusedMap0754 sourceMap0754_checked fusedMap0754_checked
    DegreeTwoThreeFiniteComparisons.comparison0754
#print axioms sourceMap0754_checked
#print axioms fusedMap0754_checked
#print axioms certified0754
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

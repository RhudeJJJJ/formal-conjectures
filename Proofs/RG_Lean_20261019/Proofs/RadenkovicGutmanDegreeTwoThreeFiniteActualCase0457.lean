/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0457 : Family 10 := level10.get ⟨256,by decide⟩
def sourceMap0457 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0457 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0457_checked : acceptsGraphIso
    (source (graph core0457) (root 10) 0 0) DegreeOneSmallSpectrum1029.graph sourceMap0457=true := by decide +kernel
theorem fusedMap0457_checked : acceptsGraphIso
    (fused (graph core0457) (root 10) 0 0) DegreeOneSmallSpectrum1237.graph fusedMap0457=true := by decide +kernel
theorem certified0457 : Certified (graph core0457) (root 10) 0 0 :=
  of_native_maps core0457 DegreeOneSmallSpectrum1029.graph DegreeOneSmallSpectrum1237.graph
    sourceMap0457 fusedMap0457 sourceMap0457_checked fusedMap0457_checked
    DegreeTwoThreeFiniteComparisons.comparison0457
#print axioms sourceMap0457_checked
#print axioms fusedMap0457_checked
#print axioms certified0457
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

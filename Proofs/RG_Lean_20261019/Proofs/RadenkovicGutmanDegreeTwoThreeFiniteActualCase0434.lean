/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0434 : Family 10 := level10.get ⟨171,by decide⟩
def sourceMap0434 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,7,8,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0434 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0434_checked : acceptsGraphIso
    (source (graph core0434) (root 10) 0 0) DegreeOneSmallSpectrum1049.graph sourceMap0434=true := by decide +kernel
theorem fusedMap0434_checked : acceptsGraphIso
    (fused (graph core0434) (root 10) 0 0) DegreeOneSmallSpectrum931.graph fusedMap0434=true := by decide +kernel
theorem certified0434 : Certified (graph core0434) (root 10) 0 0 :=
  of_native_maps core0434 DegreeOneSmallSpectrum1049.graph DegreeOneSmallSpectrum931.graph
    sourceMap0434 fusedMap0434 sourceMap0434_checked fusedMap0434_checked
    DegreeTwoThreeFiniteComparisons.comparison0434
#print axioms sourceMap0434_checked
#print axioms fusedMap0434_checked
#print axioms certified0434
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

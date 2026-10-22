/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0482 : Family 10 := level10.get ⟨340,by decide⟩
def sourceMap0482 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0482 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0482_checked : acceptsGraphIso
    (source (graph core0482) (root 10) 0 0) DegreeOneSmallSpectrum1383.graph sourceMap0482=true := by decide +kernel
theorem fusedMap0482_checked : acceptsGraphIso
    (fused (graph core0482) (root 10) 0 0) DegreeOneSmallSpectrum1338.graph fusedMap0482=true := by decide +kernel
theorem certified0482 : Certified (graph core0482) (root 10) 0 0 :=
  of_native_maps core0482 DegreeOneSmallSpectrum1383.graph DegreeOneSmallSpectrum1338.graph
    sourceMap0482 fusedMap0482 sourceMap0482_checked fusedMap0482_checked
    DegreeTwoThreeFiniteComparisons.comparison0482
#print axioms sourceMap0482_checked
#print axioms fusedMap0482_checked
#print axioms certified0482
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

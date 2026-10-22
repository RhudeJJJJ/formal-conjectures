/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0461 : Family 10 := level10.get ⟨269,by decide⟩
def sourceMap0461 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0461 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,11,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0461_checked : acceptsGraphIso
    (source (graph core0461) (root 10) 0 0) DegreeOneSmallSpectrum1024.graph sourceMap0461=true := by decide +kernel
theorem fusedMap0461_checked : acceptsGraphIso
    (fused (graph core0461) (root 10) 0 0) DegreeOneSmallSpectrum1271.graph fusedMap0461=true := by decide +kernel
theorem certified0461 : Certified (graph core0461) (root 10) 0 0 :=
  of_native_maps core0461 DegreeOneSmallSpectrum1024.graph DegreeOneSmallSpectrum1271.graph
    sourceMap0461 fusedMap0461 sourceMap0461_checked fusedMap0461_checked
    DegreeTwoThreeFiniteComparisons.comparison0461
#print axioms sourceMap0461_checked
#print axioms fusedMap0461_checked
#print axioms certified0461
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

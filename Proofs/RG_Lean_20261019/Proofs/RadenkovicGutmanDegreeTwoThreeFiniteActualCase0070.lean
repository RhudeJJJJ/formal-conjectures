/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0070 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap0070 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0070 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0070_checked : acceptsGraphIso
    (source (graph core0070) (root 8) 0 0) DegreeOneSmallSpectrum207.graph sourceMap0070=true := by decide +kernel
theorem fusedMap0070_checked : acceptsGraphIso
    (fused (graph core0070) (root 8) 0 0) DegreeOneSmallSpectrum202.graph fusedMap0070=true := by decide +kernel
theorem certified0070 : Certified (graph core0070) (root 8) 0 0 :=
  of_native_maps core0070 DegreeOneSmallSpectrum207.graph DegreeOneSmallSpectrum202.graph
    sourceMap0070 fusedMap0070 sourceMap0070_checked fusedMap0070_checked
    DegreeTwoThreeFiniteComparisons.comparison0070
#print axioms sourceMap0070_checked
#print axioms fusedMap0070_checked
#print axioms certified0070
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

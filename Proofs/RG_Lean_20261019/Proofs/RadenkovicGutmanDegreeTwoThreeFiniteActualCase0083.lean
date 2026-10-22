/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0083 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap0083 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0083 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0083_checked : acceptsGraphIso
    (source (graph core0083) (root 8) 0 0) DegreeOneSmallSpectrum258.graph sourceMap0083=true := by decide +kernel
theorem fusedMap0083_checked : acceptsGraphIso
    (fused (graph core0083) (root 8) 0 0) DegreeOneSmallSpectrum211.graph fusedMap0083=true := by decide +kernel
theorem certified0083 : Certified (graph core0083) (root 8) 0 0 :=
  of_native_maps core0083 DegreeOneSmallSpectrum258.graph DegreeOneSmallSpectrum211.graph
    sourceMap0083 fusedMap0083 sourceMap0083_checked fusedMap0083_checked
    DegreeTwoThreeFiniteComparisons.comparison0083
#print axioms sourceMap0083_checked
#print axioms fusedMap0083_checked
#print axioms certified0083
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

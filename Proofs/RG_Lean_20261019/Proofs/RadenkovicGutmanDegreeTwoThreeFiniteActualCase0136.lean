/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0136 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap0136 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0136 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0136_checked : acceptsGraphIso
    (source (graph core0136) (root 8) 0 0) DegreeOneSmallSpectrum279.graph sourceMap0136=true := by decide +kernel
theorem fusedMap0136_checked : acceptsGraphIso
    (fused (graph core0136) (root 8) 0 0) DegreeOneSmallSpectrum278.graph fusedMap0136=true := by decide +kernel
theorem certified0136 : Certified (graph core0136) (root 8) 0 0 :=
  of_native_maps core0136 DegreeOneSmallSpectrum279.graph DegreeOneSmallSpectrum278.graph
    sourceMap0136 fusedMap0136 sourceMap0136_checked fusedMap0136_checked
    DegreeTwoThreeFiniteComparisons.comparison0136
#print axioms sourceMap0136_checked
#print axioms fusedMap0136_checked
#print axioms certified0136
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0096 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap0096 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0096 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0096_checked : acceptsGraphIso
    (source (graph core0096) (root 8) 0 0) DegreeOneSmallSpectrum254.graph sourceMap0096=true := by decide +kernel
theorem fusedMap0096_checked : acceptsGraphIso
    (fused (graph core0096) (root 8) 0 0) DegreeOneSmallSpectrum298.graph fusedMap0096=true := by decide +kernel
theorem certified0096 : Certified (graph core0096) (root 8) 0 0 :=
  of_native_maps core0096 DegreeOneSmallSpectrum254.graph DegreeOneSmallSpectrum298.graph
    sourceMap0096 fusedMap0096 sourceMap0096_checked fusedMap0096_checked
    DegreeTwoThreeFiniteComparisons.comparison0096
#print axioms sourceMap0096_checked
#print axioms fusedMap0096_checked
#print axioms certified0096
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0276 : Family 9 := level9.get ⟨379,by decide⟩
def sourceMap0276 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0276 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0276_checked : acceptsGraphIso
    (source (graph core0276) (root 9) 0 0) DegreeOneSmallSpectrum645.graph sourceMap0276=true := by decide +kernel
theorem fusedMap0276_checked : acceptsGraphIso
    (fused (graph core0276) (root 9) 0 0) DegreeOneSmallSpectrum740.graph fusedMap0276=true := by decide +kernel
theorem certified0276 : Certified (graph core0276) (root 9) 0 0 :=
  of_native_maps core0276 DegreeOneSmallSpectrum645.graph DegreeOneSmallSpectrum740.graph
    sourceMap0276 fusedMap0276 sourceMap0276_checked fusedMap0276_checked
    DegreeTwoThreeFiniteComparisons.comparison0276
#print axioms sourceMap0276_checked
#print axioms fusedMap0276_checked
#print axioms certified0276
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

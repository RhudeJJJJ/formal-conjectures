/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0209 : Family 9 := level9.get ⟨192,by decide⟩
def sourceMap0209 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0209 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0209_checked : acceptsGraphIso
    (source (graph core0209) (root 9) 0 0) DegreeOneSmallSpectrum646.graph sourceMap0209=true := by decide +kernel
theorem fusedMap0209_checked : acceptsGraphIso
    (fused (graph core0209) (root 9) 0 0) DegreeOneSmallSpectrum488.graph fusedMap0209=true := by decide +kernel
theorem certified0209 : Certified (graph core0209) (root 9) 0 0 :=
  of_native_maps core0209 DegreeOneSmallSpectrum646.graph DegreeOneSmallSpectrum488.graph
    sourceMap0209 fusedMap0209 sourceMap0209_checked fusedMap0209_checked
    DegreeTwoThreeFiniteComparisons.comparison0209
#print axioms sourceMap0209_checked
#print axioms fusedMap0209_checked
#print axioms certified0209
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0108 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap0108 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0108 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0108_checked : acceptsGraphIso
    (source (graph core0108) (root 8) 0 0) DegreeTwoThreeSpectrum296.graph sourceMap0108=true := by decide +kernel
theorem fusedMap0108_checked : acceptsGraphIso
    (fused (graph core0108) (root 8) 0 0) DegreeOneSmallSpectrum327.graph fusedMap0108=true := by decide +kernel
theorem certified0108 : Certified (graph core0108) (root 8) 0 0 :=
  of_native_maps core0108 DegreeTwoThreeSpectrum296.graph DegreeOneSmallSpectrum327.graph
    sourceMap0108 fusedMap0108 sourceMap0108_checked fusedMap0108_checked
    DegreeTwoThreeFiniteComparisons.comparison0108
#print axioms sourceMap0108_checked
#print axioms fusedMap0108_checked
#print axioms certified0108
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0847 : Family 10 := level10.get ⟨1326,by decide⟩
def sourceMap0847 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0847 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0847_checked : acceptsGraphIso
    (source (graph core0847) (root 10) 0 0) DegreeTwoThreeSpectrum1643.graph sourceMap0847=true := by decide +kernel
theorem fusedMap0847_checked : acceptsGraphIso
    (fused (graph core0847) (root 10) 0 0) DegreeOneSmallSpectrum1920.graph fusedMap0847=true := by decide +kernel
theorem certified0847 : Certified (graph core0847) (root 10) 0 0 :=
  of_native_maps core0847 DegreeTwoThreeSpectrum1643.graph DegreeOneSmallSpectrum1920.graph
    sourceMap0847 fusedMap0847 sourceMap0847_checked fusedMap0847_checked
    DegreeTwoThreeFiniteComparisons.comparison0847
#print axioms sourceMap0847_checked
#print axioms fusedMap0847_checked
#print axioms certified0847
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

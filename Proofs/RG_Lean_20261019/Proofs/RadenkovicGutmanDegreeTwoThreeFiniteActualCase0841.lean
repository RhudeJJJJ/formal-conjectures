/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0841 : Family 10 := level10.get ⟨1311,by decide⟩
def sourceMap0841 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0841 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0841_checked : acceptsGraphIso
    (source (graph core0841) (root 10) 0 0) DegreeTwoThreeSpectrum1639.graph sourceMap0841=true := by decide +kernel
theorem fusedMap0841_checked : acceptsGraphIso
    (fused (graph core0841) (root 10) 0 0) DegreeOneSmallSpectrum1919.graph fusedMap0841=true := by decide +kernel
theorem certified0841 : Certified (graph core0841) (root 10) 0 0 :=
  of_native_maps core0841 DegreeTwoThreeSpectrum1639.graph DegreeOneSmallSpectrum1919.graph
    sourceMap0841 fusedMap0841 sourceMap0841_checked fusedMap0841_checked
    DegreeTwoThreeFiniteComparisons.comparison0841
#print axioms sourceMap0841_checked
#print axioms fusedMap0841_checked
#print axioms certified0841
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

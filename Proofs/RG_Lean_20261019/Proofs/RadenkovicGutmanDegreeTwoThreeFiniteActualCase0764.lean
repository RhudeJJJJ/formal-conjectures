/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0764 : Family 10 := level10.get ⟨1123,by decide⟩
def sourceMap0764 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0764 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0764_checked : acceptsGraphIso
    (source (graph core0764) (root 10) 0 0) DegreeOneSmallSpectrum1757.graph sourceMap0764=true := by decide +kernel
theorem fusedMap0764_checked : acceptsGraphIso
    (fused (graph core0764) (root 10) 0 0) DegreeOneSmallSpectrum1755.graph fusedMap0764=true := by decide +kernel
theorem certified0764 : Certified (graph core0764) (root 10) 0 0 :=
  of_native_maps core0764 DegreeOneSmallSpectrum1757.graph DegreeOneSmallSpectrum1755.graph
    sourceMap0764 fusedMap0764 sourceMap0764_checked fusedMap0764_checked
    DegreeTwoThreeFiniteComparisons.comparison0764
#print axioms sourceMap0764_checked
#print axioms fusedMap0764_checked
#print axioms certified0764
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

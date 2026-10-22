/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0830 : Family 10 := level10.get ⟨1284,by decide⟩
def sourceMap0830 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0830 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0830_checked : acceptsGraphIso
    (source (graph core0830) (root 10) 0 0) DegreeOneSmallSpectrum1329.graph sourceMap0830=true := by decide +kernel
theorem fusedMap0830_checked : acceptsGraphIso
    (fused (graph core0830) (root 10) 0 0) DegreeOneSmallSpectrum1328.graph fusedMap0830=true := by decide +kernel
theorem certified0830 : Certified (graph core0830) (root 10) 0 0 :=
  of_native_maps core0830 DegreeOneSmallSpectrum1329.graph DegreeOneSmallSpectrum1328.graph
    sourceMap0830 fusedMap0830 sourceMap0830_checked fusedMap0830_checked
    DegreeTwoThreeFiniteComparisons.comparison0830
#print axioms sourceMap0830_checked
#print axioms fusedMap0830_checked
#print axioms certified0830
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

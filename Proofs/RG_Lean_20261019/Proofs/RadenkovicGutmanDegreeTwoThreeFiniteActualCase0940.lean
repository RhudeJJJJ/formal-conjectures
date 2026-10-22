/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0940 : Family 10 := level10.get ⟨1555,by decide⟩
def sourceMap0940 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0940 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0940_checked : acceptsGraphIso
    (source (graph core0940) (root 10) 0 0) DegreeOneSmallSpectrum1579.graph sourceMap0940=true := by decide +kernel
theorem fusedMap0940_checked : acceptsGraphIso
    (fused (graph core0940) (root 10) 0 0) DegreeOneSmallSpectrum1578.graph fusedMap0940=true := by decide +kernel
theorem certified0940 : Certified (graph core0940) (root 10) 0 0 :=
  of_native_maps core0940 DegreeOneSmallSpectrum1579.graph DegreeOneSmallSpectrum1578.graph
    sourceMap0940 fusedMap0940 sourceMap0940_checked fusedMap0940_checked
    DegreeTwoThreeFiniteComparisons.comparison0940
#print axioms sourceMap0940_checked
#print axioms fusedMap0940_checked
#print axioms certified0940
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

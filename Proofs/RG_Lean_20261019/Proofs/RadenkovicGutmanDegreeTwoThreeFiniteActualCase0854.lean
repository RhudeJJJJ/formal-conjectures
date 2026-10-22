/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0854 : Family 10 := level10.get ⟨1338,by decide⟩
def sourceMap0854 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0854 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0854_checked : acceptsGraphIso
    (source (graph core0854) (root 10) 0 0) DegreeOneSmallSpectrum1382.graph sourceMap0854=true := by decide +kernel
theorem fusedMap0854_checked : acceptsGraphIso
    (fused (graph core0854) (root 10) 0 0) DegreeOneSmallSpectrum1381.graph fusedMap0854=true := by decide +kernel
theorem certified0854 : Certified (graph core0854) (root 10) 0 0 :=
  of_native_maps core0854 DegreeOneSmallSpectrum1382.graph DegreeOneSmallSpectrum1381.graph
    sourceMap0854 fusedMap0854 sourceMap0854_checked fusedMap0854_checked
    DegreeTwoThreeFiniteComparisons.comparison0854
#print axioms sourceMap0854_checked
#print axioms fusedMap0854_checked
#print axioms certified0854
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

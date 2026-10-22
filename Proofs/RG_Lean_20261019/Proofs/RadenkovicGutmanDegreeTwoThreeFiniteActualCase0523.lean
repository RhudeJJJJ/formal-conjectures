/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0523 : Family 10 := level10.get ⟨464,by decide⟩
def sourceMap0523 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0523 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0523_checked : acceptsGraphIso
    (source (graph core0523) (root 10) 0 0) DegreeOneSmallSpectrum1135.graph sourceMap0523=true := by decide +kernel
theorem fusedMap0523_checked : acceptsGraphIso
    (fused (graph core0523) (root 10) 0 0) DegreeOneSmallSpectrum1112.graph fusedMap0523=true := by decide +kernel
theorem certified0523 : Certified (graph core0523) (root 10) 0 0 :=
  of_native_maps core0523 DegreeOneSmallSpectrum1135.graph DegreeOneSmallSpectrum1112.graph
    sourceMap0523 fusedMap0523 sourceMap0523_checked fusedMap0523_checked
    DegreeTwoThreeFiniteComparisons.comparison0523
#print axioms sourceMap0523_checked
#print axioms fusedMap0523_checked
#print axioms certified0523
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

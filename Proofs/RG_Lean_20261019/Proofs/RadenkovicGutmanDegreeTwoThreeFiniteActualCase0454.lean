/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0454 : Family 10 := level10.get ⟨245,by decide⟩
def sourceMap0454 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0454 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0454_checked : acceptsGraphIso
    (source (graph core0454) (root 10) 0 0) DegreeOneSmallSpectrum1064.graph sourceMap0454=true := by decide +kernel
theorem fusedMap0454_checked : acceptsGraphIso
    (fused (graph core0454) (root 10) 0 0) DegreeOneSmallSpectrum1207.graph fusedMap0454=true := by decide +kernel
theorem certified0454 : Certified (graph core0454) (root 10) 0 0 :=
  of_native_maps core0454 DegreeOneSmallSpectrum1064.graph DegreeOneSmallSpectrum1207.graph
    sourceMap0454 fusedMap0454 sourceMap0454_checked fusedMap0454_checked
    DegreeTwoThreeFiniteComparisons.comparison0454
#print axioms sourceMap0454_checked
#print axioms fusedMap0454_checked
#print axioms certified0454
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

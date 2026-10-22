/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0411 : Family 10 := level10.get ⟨77,by decide⟩
def sourceMap0411 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0411 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0411_checked : acceptsGraphIso
    (source (graph core0411) (root 10) 0 0) DegreeOneSmallSpectrum1067.graph sourceMap0411=true := by decide +kernel
theorem fusedMap0411_checked : acceptsGraphIso
    (fused (graph core0411) (root 10) 0 0) DegreeOneSmallSpectrum891.graph fusedMap0411=true := by decide +kernel
theorem certified0411 : Certified (graph core0411) (root 10) 0 0 :=
  of_native_maps core0411 DegreeOneSmallSpectrum1067.graph DegreeOneSmallSpectrum891.graph
    sourceMap0411 fusedMap0411 sourceMap0411_checked fusedMap0411_checked
    DegreeTwoThreeFiniteComparisons.comparison0411
#print axioms sourceMap0411_checked
#print axioms fusedMap0411_checked
#print axioms certified0411
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

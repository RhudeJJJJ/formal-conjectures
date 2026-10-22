/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0822 : Family 10 := level10.get ⟨1265,by decide⟩
def sourceMap0822 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0822 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0822_checked : acceptsGraphIso
    (source (graph core0822) (root 10) 0 0) DegreeOneSmallSpectrum1311.graph sourceMap0822=true := by decide +kernel
theorem fusedMap0822_checked : acceptsGraphIso
    (fused (graph core0822) (root 10) 0 0) DegreeOneSmallSpectrum1310.graph fusedMap0822=true := by decide +kernel
theorem certified0822 : Certified (graph core0822) (root 10) 0 0 :=
  of_native_maps core0822 DegreeOneSmallSpectrum1311.graph DegreeOneSmallSpectrum1310.graph
    sourceMap0822 fusedMap0822 sourceMap0822_checked fusedMap0822_checked
    DegreeTwoThreeFiniteComparisons.comparison0822
#print axioms sourceMap0822_checked
#print axioms fusedMap0822_checked
#print axioms certified0822
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

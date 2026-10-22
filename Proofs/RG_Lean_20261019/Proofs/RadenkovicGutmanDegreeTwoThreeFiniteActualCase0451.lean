/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0451 : Family 10 := level10.get ⟨234,by decide⟩
def sourceMap0451 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0451 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0451_checked : acceptsGraphIso
    (source (graph core0451) (root 10) 0 0) DegreeOneSmallSpectrum1050.graph sourceMap0451=true := by decide +kernel
theorem fusedMap0451_checked : acceptsGraphIso
    (fused (graph core0451) (root 10) 0 0) DegreeOneSmallSpectrum1173.graph fusedMap0451=true := by decide +kernel
theorem certified0451 : Certified (graph core0451) (root 10) 0 0 :=
  of_native_maps core0451 DegreeOneSmallSpectrum1050.graph DegreeOneSmallSpectrum1173.graph
    sourceMap0451 fusedMap0451 sourceMap0451_checked fusedMap0451_checked
    DegreeTwoThreeFiniteComparisons.comparison0451
#print axioms sourceMap0451_checked
#print axioms fusedMap0451_checked
#print axioms certified0451
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

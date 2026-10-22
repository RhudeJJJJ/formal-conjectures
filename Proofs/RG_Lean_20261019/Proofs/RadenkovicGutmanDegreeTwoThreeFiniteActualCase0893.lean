/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0893 : Family 10 := level10.get ⟨1432,by decide⟩
def sourceMap0893 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0893 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0893_checked : acceptsGraphIso
    (source (graph core0893) (root 10) 0 0) DegreeOneSmallSpectrum1473.graph sourceMap0893=true := by decide +kernel
theorem fusedMap0893_checked : acceptsGraphIso
    (fused (graph core0893) (root 10) 0 0) DegreeOneSmallSpectrum1472.graph fusedMap0893=true := by decide +kernel
theorem certified0893 : Certified (graph core0893) (root 10) 0 0 :=
  of_native_maps core0893 DegreeOneSmallSpectrum1473.graph DegreeOneSmallSpectrum1472.graph
    sourceMap0893 fusedMap0893 sourceMap0893_checked fusedMap0893_checked
    DegreeTwoThreeFiniteComparisons.comparison0893
#print axioms sourceMap0893_checked
#print axioms fusedMap0893_checked
#print axioms certified0893
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

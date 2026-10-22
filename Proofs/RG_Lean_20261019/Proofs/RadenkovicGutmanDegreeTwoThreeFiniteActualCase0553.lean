/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0553 : Family 10 := level10.get ⟨555,by decide⟩
def sourceMap0553 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0553 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0553_checked : acceptsGraphIso
    (source (graph core0553) (root 10) 0 0) DegreeOneSmallSpectrum1079.graph sourceMap0553=true := by decide +kernel
theorem fusedMap0553_checked : acceptsGraphIso
    (fused (graph core0553) (root 10) 0 0) DegreeOneSmallSpectrum1077.graph fusedMap0553=true := by decide +kernel
theorem certified0553 : Certified (graph core0553) (root 10) 0 0 :=
  of_native_maps core0553 DegreeOneSmallSpectrum1079.graph DegreeOneSmallSpectrum1077.graph
    sourceMap0553 fusedMap0553 sourceMap0553_checked fusedMap0553_checked
    DegreeTwoThreeFiniteComparisons.comparison0553
#print axioms sourceMap0553_checked
#print axioms fusedMap0553_checked
#print axioms certified0553
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

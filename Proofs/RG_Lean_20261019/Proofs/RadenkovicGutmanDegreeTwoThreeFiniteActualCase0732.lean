/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0732 : Family 10 := level10.get ⟨1043,by decide⟩
def sourceMap0732 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0732 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0732_checked : acceptsGraphIso
    (source (graph core0732) (root 10) 0 0) DegreeTwoThreeSpectrum1390.graph sourceMap0732=true := by decide +kernel
theorem fusedMap0732_checked : acceptsGraphIso
    (fused (graph core0732) (root 10) 0 0) DegreeOneSmallSpectrum1634.graph fusedMap0732=true := by decide +kernel
theorem certified0732 : Certified (graph core0732) (root 10) 0 0 :=
  of_native_maps core0732 DegreeTwoThreeSpectrum1390.graph DegreeOneSmallSpectrum1634.graph
    sourceMap0732 fusedMap0732 sourceMap0732_checked fusedMap0732_checked
    DegreeTwoThreeFiniteComparisons.comparison0732
#print axioms sourceMap0732_checked
#print axioms fusedMap0732_checked
#print axioms certified0732
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

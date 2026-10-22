/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0543 : Family 10 := level10.get ⟨528,by decide⟩
def sourceMap0543 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0543 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0543_checked : acceptsGraphIso
    (source (graph core0543) (root 10) 0 0) DegreeTwoThreeSpectrum1419.graph sourceMap0543=true := by decide +kernel
theorem fusedMap0543_checked : acceptsGraphIso
    (fused (graph core0543) (root 10) 0 0) DegreeOneSmallSpectrum1025.graph fusedMap0543=true := by decide +kernel
theorem certified0543 : Certified (graph core0543) (root 10) 0 0 :=
  of_native_maps core0543 DegreeTwoThreeSpectrum1419.graph DegreeOneSmallSpectrum1025.graph
    sourceMap0543 fusedMap0543 sourceMap0543_checked fusedMap0543_checked
    DegreeTwoThreeFiniteComparisons.comparison0543
#print axioms sourceMap0543_checked
#print axioms fusedMap0543_checked
#print axioms certified0543
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0551 : Family 10 := level10.get ⟨552,by decide⟩
def sourceMap0551 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0551 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0551_checked : acceptsGraphIso
    (source (graph core0551) (root 10) 0 0) DegreeTwoThreeSpectrum1406.graph sourceMap0551=true := by decide +kernel
theorem fusedMap0551_checked : acceptsGraphIso
    (fused (graph core0551) (root 10) 0 0) DegreeOneSmallSpectrum1071.graph fusedMap0551=true := by decide +kernel
theorem certified0551 : Certified (graph core0551) (root 10) 0 0 :=
  of_native_maps core0551 DegreeTwoThreeSpectrum1406.graph DegreeOneSmallSpectrum1071.graph
    sourceMap0551 fusedMap0551 sourceMap0551_checked fusedMap0551_checked
    DegreeTwoThreeFiniteComparisons.comparison0551
#print axioms sourceMap0551_checked
#print axioms fusedMap0551_checked
#print axioms certified0551
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

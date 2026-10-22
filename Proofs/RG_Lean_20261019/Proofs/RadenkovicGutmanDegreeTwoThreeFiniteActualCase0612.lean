/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0612 : Family 10 := level10.get ⟨728,by decide⟩
def sourceMap0612 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0612 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0612_checked : acceptsGraphIso
    (source (graph core0612) (root 10) 0 0) DegreeTwoThreeSpectrum1466.graph sourceMap0612=true := by decide +kernel
theorem fusedMap0612_checked : acceptsGraphIso
    (fused (graph core0612) (root 10) 0 0) DegreeOneSmallSpectrum1351.graph fusedMap0612=true := by decide +kernel
theorem certified0612 : Certified (graph core0612) (root 10) 0 0 :=
  of_native_maps core0612 DegreeTwoThreeSpectrum1466.graph DegreeOneSmallSpectrum1351.graph
    sourceMap0612 fusedMap0612 sourceMap0612_checked fusedMap0612_checked
    DegreeTwoThreeFiniteComparisons.comparison0612
#print axioms sourceMap0612_checked
#print axioms fusedMap0612_checked
#print axioms certified0612
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

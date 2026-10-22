/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0621 : Family 10 := level10.get ⟨756,by decide⟩
def sourceMap0621 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0621 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0621_checked : acceptsGraphIso
    (source (graph core0621) (root 10) 0 0) DegreeTwoThreeSpectrum1414.graph sourceMap0621=true := by decide +kernel
theorem fusedMap0621_checked : acceptsGraphIso
    (fused (graph core0621) (root 10) 0 0) DegreeOneSmallSpectrum1382.graph fusedMap0621=true := by decide +kernel
theorem certified0621 : Certified (graph core0621) (root 10) 0 0 :=
  of_native_maps core0621 DegreeTwoThreeSpectrum1414.graph DegreeOneSmallSpectrum1382.graph
    sourceMap0621 fusedMap0621 sourceMap0621_checked fusedMap0621_checked
    DegreeTwoThreeFiniteComparisons.comparison0621
#print axioms sourceMap0621_checked
#print axioms fusedMap0621_checked
#print axioms certified0621
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

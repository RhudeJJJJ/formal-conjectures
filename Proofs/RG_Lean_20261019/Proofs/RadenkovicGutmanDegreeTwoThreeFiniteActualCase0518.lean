/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0518 : Family 10 := level10.get ⟨453,by decide⟩
def sourceMap0518 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0518 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0518_checked : acceptsGraphIso
    (source (graph core0518) (root 10) 0 0) DegreeOneSmallSpectrum1393.graph sourceMap0518=true := by decide +kernel
theorem fusedMap0518_checked : acceptsGraphIso
    (fused (graph core0518) (root 10) 0 0) DegreeOneSmallSpectrum1348.graph fusedMap0518=true := by decide +kernel
theorem certified0518 : Certified (graph core0518) (root 10) 0 0 :=
  of_native_maps core0518 DegreeOneSmallSpectrum1393.graph DegreeOneSmallSpectrum1348.graph
    sourceMap0518 fusedMap0518 sourceMap0518_checked fusedMap0518_checked
    DegreeTwoThreeFiniteComparisons.comparison0518
#print axioms sourceMap0518_checked
#print axioms fusedMap0518_checked
#print axioms certified0518
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

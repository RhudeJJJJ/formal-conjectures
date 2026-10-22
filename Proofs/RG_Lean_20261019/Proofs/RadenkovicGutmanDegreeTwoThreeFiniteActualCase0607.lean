/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0607 : Family 10 := level10.get ⟨716,by decide⟩
def sourceMap0607 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0607 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0607_checked : acceptsGraphIso
    (source (graph core0607) (root 10) 0 0) DegreeOneSmallSpectrum1634.graph sourceMap0607=true := by decide +kernel
theorem fusedMap0607_checked : acceptsGraphIso
    (fused (graph core0607) (root 10) 0 0) DegreeOneSmallSpectrum1336.graph fusedMap0607=true := by decide +kernel
theorem certified0607 : Certified (graph core0607) (root 10) 0 0 :=
  of_native_maps core0607 DegreeOneSmallSpectrum1634.graph DegreeOneSmallSpectrum1336.graph
    sourceMap0607 fusedMap0607 sourceMap0607_checked fusedMap0607_checked
    DegreeTwoThreeFiniteComparisons.comparison0607
#print axioms sourceMap0607_checked
#print axioms fusedMap0607_checked
#print axioms certified0607
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

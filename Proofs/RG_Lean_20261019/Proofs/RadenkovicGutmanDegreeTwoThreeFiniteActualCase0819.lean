/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0819 : Family 10 := level10.get ⟨1260,by decide⟩
def sourceMap0819 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0819 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0819_checked : acceptsGraphIso
    (source (graph core0819) (root 10) 0 0) DegreeTwoThreeSpectrum1387.graph sourceMap0819=true := by decide +kernel
theorem fusedMap0819_checked : acceptsGraphIso
    (fused (graph core0819) (root 10) 0 0) DegreeOneSmallSpectrum1909.graph fusedMap0819=true := by decide +kernel
theorem certified0819 : Certified (graph core0819) (root 10) 0 0 :=
  of_native_maps core0819 DegreeTwoThreeSpectrum1387.graph DegreeOneSmallSpectrum1909.graph
    sourceMap0819 fusedMap0819 sourceMap0819_checked fusedMap0819_checked
    DegreeTwoThreeFiniteComparisons.comparison0819
#print axioms sourceMap0819_checked
#print axioms fusedMap0819_checked
#print axioms certified0819
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

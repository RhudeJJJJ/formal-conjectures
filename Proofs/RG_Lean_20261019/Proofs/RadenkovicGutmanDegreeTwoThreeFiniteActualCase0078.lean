/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0078 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap0078 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0078 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0078_checked : acceptsGraphIso
    (source (graph core0078) (root 8) 0 0) DegreeOneSmallSpectrum264.graph sourceMap0078=true := by decide +kernel
theorem fusedMap0078_checked : acceptsGraphIso
    (fused (graph core0078) (root 8) 0 0) DegreeOneSmallSpectrum210.graph fusedMap0078=true := by decide +kernel
theorem certified0078 : Certified (graph core0078) (root 8) 0 0 :=
  of_native_maps core0078 DegreeOneSmallSpectrum264.graph DegreeOneSmallSpectrum210.graph
    sourceMap0078 fusedMap0078 sourceMap0078_checked fusedMap0078_checked
    DegreeTwoThreeFiniteComparisons.comparison0078
#print axioms sourceMap0078_checked
#print axioms fusedMap0078_checked
#print axioms certified0078
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

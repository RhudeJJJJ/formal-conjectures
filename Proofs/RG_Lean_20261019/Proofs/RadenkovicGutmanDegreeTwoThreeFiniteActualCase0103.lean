/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0103 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap0103 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0103 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0103_checked : acceptsGraphIso
    (source (graph core0103) (root 8) 0 0) DegreeTwoThreeSpectrum241.graph sourceMap0103=true := by decide +kernel
theorem fusedMap0103_checked : acceptsGraphIso
    (fused (graph core0103) (root 8) 0 0) DegreeOneSmallSpectrum323.graph fusedMap0103=true := by decide +kernel
theorem certified0103 : Certified (graph core0103) (root 8) 0 0 :=
  of_native_maps core0103 DegreeTwoThreeSpectrum241.graph DegreeOneSmallSpectrum323.graph
    sourceMap0103 fusedMap0103 sourceMap0103_checked fusedMap0103_checked
    DegreeTwoThreeFiniteComparisons.comparison0103
#print axioms sourceMap0103_checked
#print axioms fusedMap0103_checked
#print axioms certified0103
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

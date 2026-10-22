/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0100 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap0100 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,10,6,7,8,9] (sourceLabel 8 0 0 v)
def fusedMap0100 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,10,6,7,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0100_checked : acceptsGraphIso
    (source (graph core0100) (root 8) 0 0) DegreeOneSmallSpectrum309.graph sourceMap0100=true := by decide +kernel
theorem fusedMap0100_checked : acceptsGraphIso
    (fused (graph core0100) (root 8) 0 0) DegreeOneSmallSpectrum306.graph fusedMap0100=true := by decide +kernel
theorem certified0100 : Certified (graph core0100) (root 8) 0 0 :=
  of_native_maps core0100 DegreeOneSmallSpectrum309.graph DegreeOneSmallSpectrum306.graph
    sourceMap0100 fusedMap0100 sourceMap0100_checked fusedMap0100_checked
    DegreeTwoThreeFiniteComparisons.comparison0100
#print axioms sourceMap0100_checked
#print axioms fusedMap0100_checked
#print axioms certified0100
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

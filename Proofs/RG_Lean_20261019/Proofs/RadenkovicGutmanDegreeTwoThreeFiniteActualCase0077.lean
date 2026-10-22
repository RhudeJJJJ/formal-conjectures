/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0077 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap0077 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0077 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0077_checked : acceptsGraphIso
    (source (graph core0077) (root 8) 0 0) DegreeTwoThreeSpectrum244.graph sourceMap0077=true := by decide +kernel
theorem fusedMap0077_checked : acceptsGraphIso
    (fused (graph core0077) (root 8) 0 0) DegreeOneSmallSpectrum205.graph fusedMap0077=true := by decide +kernel
theorem certified0077 : Certified (graph core0077) (root 8) 0 0 :=
  of_native_maps core0077 DegreeTwoThreeSpectrum244.graph DegreeOneSmallSpectrum205.graph
    sourceMap0077 fusedMap0077 sourceMap0077_checked fusedMap0077_checked
    DegreeTwoThreeFiniteComparisons.comparison0077
#print axioms sourceMap0077_checked
#print axioms fusedMap0077_checked
#print axioms certified0077
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

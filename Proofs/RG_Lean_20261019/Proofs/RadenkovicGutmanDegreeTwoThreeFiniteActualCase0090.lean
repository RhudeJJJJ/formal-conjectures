/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0090 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap0090 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0090 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0090_checked : acceptsGraphIso
    (source (graph core0090) (root 8) 0 0) DegreeTwoThreeSpectrum216.graph sourceMap0090=true := by decide +kernel
theorem fusedMap0090_checked : acceptsGraphIso
    (fused (graph core0090) (root 8) 0 0) DegreeOneSmallSpectrum243.graph fusedMap0090=true := by decide +kernel
theorem certified0090 : Certified (graph core0090) (root 8) 0 0 :=
  of_native_maps core0090 DegreeTwoThreeSpectrum216.graph DegreeOneSmallSpectrum243.graph
    sourceMap0090 fusedMap0090 sourceMap0090_checked fusedMap0090_checked
    DegreeTwoThreeFiniteComparisons.comparison0090
#print axioms sourceMap0090_checked
#print axioms fusedMap0090_checked
#print axioms certified0090
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

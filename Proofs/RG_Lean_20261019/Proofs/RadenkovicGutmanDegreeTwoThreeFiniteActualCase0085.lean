/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0085 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap0085 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,8,9,10,6,7,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0085 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0085_checked : acceptsGraphIso
    (source (graph core0085) (root 8) 0 0) DegreeOneSmallSpectrum249.graph sourceMap0085=true := by decide +kernel
theorem fusedMap0085_checked : acceptsGraphIso
    (fused (graph core0085) (root 8) 0 0) DegreeOneSmallSpectrum208.graph fusedMap0085=true := by decide +kernel
theorem certified0085 : Certified (graph core0085) (root 8) 0 0 :=
  of_native_maps core0085 DegreeOneSmallSpectrum249.graph DegreeOneSmallSpectrum208.graph
    sourceMap0085 fusedMap0085 sourceMap0085_checked fusedMap0085_checked
    DegreeTwoThreeFiniteComparisons.comparison0085
#print axioms sourceMap0085_checked
#print axioms fusedMap0085_checked
#print axioms certified0085
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

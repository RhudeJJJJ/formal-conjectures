/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0012 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap0012 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0012 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0012_checked : acceptsGraphIso
    (source (graph core0012) (root 6) 0 0) DegreeOneSmallSpectrum040.graph sourceMap0012=true := by decide +kernel
theorem fusedMap0012_checked : acceptsGraphIso
    (fused (graph core0012) (root 6) 0 0) DegreeOneSmallSpectrum051.graph fusedMap0012=true := by decide +kernel
theorem certified0012 : Certified (graph core0012) (root 6) 0 0 :=
  of_native_maps core0012 DegreeOneSmallSpectrum040.graph DegreeOneSmallSpectrum051.graph
    sourceMap0012 fusedMap0012 sourceMap0012_checked fusedMap0012_checked
    DegreeTwoThreeFiniteComparisons.comparison0012
#print axioms sourceMap0012_checked
#print axioms fusedMap0012_checked
#print axioms certified0012
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

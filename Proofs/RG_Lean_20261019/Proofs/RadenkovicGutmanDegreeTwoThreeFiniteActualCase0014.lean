/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0014 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap0014 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,5,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0014 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap0014_checked : acceptsGraphIso
    (source (graph core0014) (root 6) 0 0) DegreeOneSmallSpectrum039.graph sourceMap0014=true := by decide +kernel
theorem fusedMap0014_checked : acceptsGraphIso
    (fused (graph core0014) (root 6) 0 0) DegreeOneSmallSpectrum060.graph fusedMap0014=true := by decide +kernel
theorem certified0014 : Certified (graph core0014) (root 6) 0 0 :=
  of_native_maps core0014 DegreeOneSmallSpectrum039.graph DegreeOneSmallSpectrum060.graph
    sourceMap0014 fusedMap0014 sourceMap0014_checked fusedMap0014_checked
    DegreeTwoThreeFiniteComparisons.comparison0014
#print axioms sourceMap0014_checked
#print axioms fusedMap0014_checked
#print axioms certified0014
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

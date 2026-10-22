/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0286 : Family 9 := level9.get ⟨402,by decide⟩
def sourceMap0286 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0286 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0286_checked : acceptsGraphIso
    (source (graph core0286) (root 9) 0 0) DegreeOneSmallSpectrum477.graph sourceMap0286=true := by decide +kernel
theorem fusedMap0286_checked : acceptsGraphIso
    (fused (graph core0286) (root 9) 0 0) DegreeOneSmallSpectrum476.graph fusedMap0286=true := by decide +kernel
theorem certified0286 : Certified (graph core0286) (root 9) 0 0 :=
  of_native_maps core0286 DegreeOneSmallSpectrum477.graph DegreeOneSmallSpectrum476.graph
    sourceMap0286 fusedMap0286 sourceMap0286_checked fusedMap0286_checked
    DegreeTwoThreeFiniteComparisons.comparison0286
#print axioms sourceMap0286_checked
#print axioms fusedMap0286_checked
#print axioms certified0286
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

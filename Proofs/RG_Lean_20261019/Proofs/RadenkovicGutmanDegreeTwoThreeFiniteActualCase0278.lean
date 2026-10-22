/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0278 : Family 9 := level9.get ⟨382,by decide⟩
def sourceMap0278 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0278 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0278_checked : acceptsGraphIso
    (source (graph core0278) (root 9) 0 0) DegreeOneSmallSpectrum455.graph sourceMap0278=true := by decide +kernel
theorem fusedMap0278_checked : acceptsGraphIso
    (fused (graph core0278) (root 9) 0 0) DegreeOneSmallSpectrum454.graph fusedMap0278=true := by decide +kernel
theorem certified0278 : Certified (graph core0278) (root 9) 0 0 :=
  of_native_maps core0278 DegreeOneSmallSpectrum455.graph DegreeOneSmallSpectrum454.graph
    sourceMap0278 fusedMap0278 sourceMap0278_checked fusedMap0278_checked
    DegreeTwoThreeFiniteComparisons.comparison0278
#print axioms sourceMap0278_checked
#print axioms fusedMap0278_checked
#print axioms certified0278
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

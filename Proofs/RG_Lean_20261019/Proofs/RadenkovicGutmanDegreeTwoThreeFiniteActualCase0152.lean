/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0152 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap0152 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0152 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0152_checked : acceptsGraphIso
    (source (graph core0152) (root 8) 0 0) DegreeOneSmallSpectrum289.graph sourceMap0152=true := by decide +kernel
theorem fusedMap0152_checked : acceptsGraphIso
    (fused (graph core0152) (root 8) 0 0) DegreeOneSmallSpectrum279.graph fusedMap0152=true := by decide +kernel
theorem certified0152 : Certified (graph core0152) (root 8) 0 0 :=
  of_native_maps core0152 DegreeOneSmallSpectrum289.graph DegreeOneSmallSpectrum279.graph
    sourceMap0152 fusedMap0152 sourceMap0152_checked fusedMap0152_checked
    DegreeTwoThreeFiniteComparisons.comparison0152
#print axioms sourceMap0152_checked
#print axioms fusedMap0152_checked
#print axioms certified0152
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

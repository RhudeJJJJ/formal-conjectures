/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0147 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap0147 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0147 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0147_checked : acceptsGraphIso
    (source (graph core0147) (root 8) 0 0) DegreeOneSmallSpectrum330.graph sourceMap0147=true := by decide +kernel
theorem fusedMap0147_checked : acceptsGraphIso
    (fused (graph core0147) (root 8) 0 0) DegreeOneSmallSpectrum329.graph fusedMap0147=true := by decide +kernel
theorem certified0147 : Certified (graph core0147) (root 8) 0 0 :=
  of_native_maps core0147 DegreeOneSmallSpectrum330.graph DegreeOneSmallSpectrum329.graph
    sourceMap0147 fusedMap0147 sourceMap0147_checked fusedMap0147_checked
    DegreeTwoThreeFiniteComparisons.comparison0147
#print axioms sourceMap0147_checked
#print axioms fusedMap0147_checked
#print axioms certified0147
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

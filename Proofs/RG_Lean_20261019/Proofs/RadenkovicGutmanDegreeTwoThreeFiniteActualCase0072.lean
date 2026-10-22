/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0072 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap0072 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0072 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0072_checked : acceptsGraphIso
    (source (graph core0072) (root 8) 0 0) DegreeOneSmallSpectrum261.graph sourceMap0072=true := by decide +kernel
theorem fusedMap0072_checked : acceptsGraphIso
    (fused (graph core0072) (root 8) 0 0) DegreeOneSmallSpectrum180.graph fusedMap0072=true := by decide +kernel
theorem certified0072 : Certified (graph core0072) (root 8) 0 0 :=
  of_native_maps core0072 DegreeOneSmallSpectrum261.graph DegreeOneSmallSpectrum180.graph
    sourceMap0072 fusedMap0072 sourceMap0072_checked fusedMap0072_checked
    DegreeTwoThreeFiniteComparisons.comparison0072
#print axioms sourceMap0072_checked
#print axioms fusedMap0072_checked
#print axioms certified0072
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

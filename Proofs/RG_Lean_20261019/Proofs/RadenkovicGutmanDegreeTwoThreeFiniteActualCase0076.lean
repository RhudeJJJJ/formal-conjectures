/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0076 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap0076 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0076 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0076_checked : acceptsGraphIso
    (source (graph core0076) (root 8) 0 0) DegreeOneSmallSpectrum263.graph sourceMap0076=true := by decide +kernel
theorem fusedMap0076_checked : acceptsGraphIso
    (fused (graph core0076) (root 8) 0 0) DegreeOneSmallSpectrum200.graph fusedMap0076=true := by decide +kernel
theorem certified0076 : Certified (graph core0076) (root 8) 0 0 :=
  of_native_maps core0076 DegreeOneSmallSpectrum263.graph DegreeOneSmallSpectrum200.graph
    sourceMap0076 fusedMap0076 sourceMap0076_checked fusedMap0076_checked
    DegreeTwoThreeFiniteComparisons.comparison0076
#print axioms sourceMap0076_checked
#print axioms fusedMap0076_checked
#print axioms certified0076
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

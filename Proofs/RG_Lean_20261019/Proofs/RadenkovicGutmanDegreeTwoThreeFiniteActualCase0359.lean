/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0359 : Family 9 := level9.get ⟨577,by decide⟩
def sourceMap0359 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0359 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0359_checked : acceptsGraphIso
    (source (graph core0359) (root 9) 0 0) DegreeOneSmallSpectrum665.graph sourceMap0359=true := by decide +kernel
theorem fusedMap0359_checked : acceptsGraphIso
    (fused (graph core0359) (root 9) 0 0) DegreeOneSmallSpectrum664.graph fusedMap0359=true := by decide +kernel
theorem certified0359 : Certified (graph core0359) (root 9) 0 0 :=
  of_native_maps core0359 DegreeOneSmallSpectrum665.graph DegreeOneSmallSpectrum664.graph
    sourceMap0359 fusedMap0359 sourceMap0359_checked fusedMap0359_checked
    DegreeTwoThreeFiniteComparisons.comparison0359
#print axioms sourceMap0359_checked
#print axioms fusedMap0359_checked
#print axioms certified0359
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

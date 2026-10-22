/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0985 : Family 10 := level10.get ⟨1662,by decide⟩
def sourceMap0985 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0985 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0985_checked : acceptsGraphIso
    (source (graph core0985) (root 10) 0 0) DegreeOneSmallSpectrum1812.graph sourceMap0985=true := by decide +kernel
theorem fusedMap0985_checked : acceptsGraphIso
    (fused (graph core0985) (root 10) 0 0) DegreeOneSmallSpectrum1811.graph fusedMap0985=true := by decide +kernel
theorem certified0985 : Certified (graph core0985) (root 10) 0 0 :=
  of_native_maps core0985 DegreeOneSmallSpectrum1812.graph DegreeOneSmallSpectrum1811.graph
    sourceMap0985 fusedMap0985 sourceMap0985_checked fusedMap0985_checked
    DegreeTwoThreeFiniteComparisons.comparison0985
#print axioms sourceMap0985_checked
#print axioms fusedMap0985_checked
#print axioms certified0985
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

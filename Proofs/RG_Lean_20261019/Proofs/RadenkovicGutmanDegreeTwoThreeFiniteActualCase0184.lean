/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0184 : Family 9 := level9.get ⟨110,by decide⟩
def sourceMap0184 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0184 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0184_checked : acceptsGraphIso
    (source (graph core0184) (root 9) 0 0) DegreeOneSmallSpectrum533.graph sourceMap0184=true := by decide +kernel
theorem fusedMap0184_checked : acceptsGraphIso
    (fused (graph core0184) (root 9) 0 0) DegreeOneSmallSpectrum517.graph fusedMap0184=true := by decide +kernel
theorem certified0184 : Certified (graph core0184) (root 9) 0 0 :=
  of_native_maps core0184 DegreeOneSmallSpectrum533.graph DegreeOneSmallSpectrum517.graph
    sourceMap0184 fusedMap0184 sourceMap0184_checked fusedMap0184_checked
    DegreeTwoThreeFiniteComparisons.comparison0184
#print axioms sourceMap0184_checked
#print axioms fusedMap0184_checked
#print axioms certified0184
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

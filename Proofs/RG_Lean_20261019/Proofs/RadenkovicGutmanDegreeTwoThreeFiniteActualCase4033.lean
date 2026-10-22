/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4033 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap4033 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,7,8,1,2,3,4,5,6] (sourceLabel 2 2 2 v)
def fusedMap4033 : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 2 2 v)
theorem sourceMap4033_checked : acceptsGraphIso
    (source (graph core4033) (root 2) 2 2) DegreeOneSmallSpectrum062.graph sourceMap4033=true := by decide +kernel
theorem fusedMap4033_checked : acceptsGraphIso
    (fused (graph core4033) (root 2) 2 2) DegreeOneSmallSpectrum034.graph fusedMap4033=true := by decide +kernel
theorem certified4033 : Certified (graph core4033) (root 2) 2 2 :=
  of_native_maps core4033 DegreeOneSmallSpectrum062.graph DegreeOneSmallSpectrum034.graph
    sourceMap4033 fusedMap4033 sourceMap4033_checked fusedMap4033_checked
    DegreeTwoThreeFiniteComparisons.comparison4033
#print axioms sourceMap4033_checked
#print axioms fusedMap4033_checked
#print axioms certified4033
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

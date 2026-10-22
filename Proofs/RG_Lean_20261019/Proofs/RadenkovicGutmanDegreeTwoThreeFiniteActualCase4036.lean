/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4036 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap4036 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 4 2 2 v)
def fusedMap4036 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap4036_checked : acceptsGraphIso
    (source (graph core4036) (root 4) 2 2) DegreeOneSmallSpectrum347.graph sourceMap4036=true := by decide +kernel
theorem fusedMap4036_checked : acceptsGraphIso
    (fused (graph core4036) (root 4) 2 2) DegreeOneSmallSpectrum182.graph fusedMap4036=true := by decide +kernel
theorem certified4036 : Certified (graph core4036) (root 4) 2 2 :=
  of_native_maps core4036 DegreeOneSmallSpectrum347.graph DegreeOneSmallSpectrum182.graph
    sourceMap4036 fusedMap4036 sourceMap4036_checked fusedMap4036_checked
    DegreeTwoThreeFiniteComparisons.comparison4036
#print axioms sourceMap4036_checked
#print axioms fusedMap4036_checked
#print axioms certified4036
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

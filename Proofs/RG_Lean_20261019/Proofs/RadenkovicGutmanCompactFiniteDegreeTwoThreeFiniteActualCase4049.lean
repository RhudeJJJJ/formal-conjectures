/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4049 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap4049 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,12,6,7,8,9,10,11] (sourceLabel 6 2 2 v)
def fusedMap4049 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4049_checked : acceptsGraphIso
    (source (graph core4049) (root 6) 2 2) DegreeOneSmallSpectrum1691.graph sourceMap4049=true := by decide +kernel
theorem fusedMap4049_checked : acceptsGraphIso
    (fused (graph core4049) (root 6) 2 2) DegreeOneSmallSpectrum864.graph fusedMap4049=true := by decide +kernel
theorem certified4049 : Certified (graph core4049) (root 6) 2 2 :=
  of_native_maps core4049 DegreeOneSmallSpectrum1691.graph DegreeOneSmallSpectrum864.graph
    sourceMap4049 fusedMap4049 sourceMap4049_checked fusedMap4049_checked
    DegreeTwoThreeFiniteComparisons.comparison4049
#print axioms sourceMap4049_checked
#print axioms fusedMap4049_checked
#print axioms certified4049
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

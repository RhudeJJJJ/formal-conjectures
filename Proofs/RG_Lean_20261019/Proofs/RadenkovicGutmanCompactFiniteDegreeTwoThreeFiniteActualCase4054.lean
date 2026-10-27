/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4054 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap4054 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,11,12,5,6,7,8,9,10] (sourceLabel 6 2 2 v)
def fusedMap4054 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4054_checked : acceptsGraphIso
    (source (graph core4054) (root 6) 2 2) DegreeOneSmallSpectrum1963.graph sourceMap4054=true := by decide +kernel
theorem fusedMap4054_checked : acceptsGraphIso
    (fused (graph core4054) (root 6) 2 2) DegreeOneSmallSpectrum923.graph fusedMap4054=true := by decide +kernel
theorem certified4054 : Certified (graph core4054) (root 6) 2 2 :=
  of_native_maps core4054 DegreeOneSmallSpectrum1963.graph DegreeOneSmallSpectrum923.graph
    sourceMap4054 fusedMap4054 sourceMap4054_checked fusedMap4054_checked
    DegreeTwoThreeFiniteComparisons.comparison4054
#print axioms sourceMap4054_checked
#print axioms fusedMap4054_checked
#print axioms certified4054
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

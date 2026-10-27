/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4056 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap4056 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,10,11,12,4,5,6,7,8,9] (sourceLabel 6 2 2 v)
def fusedMap4056 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4056_checked : acceptsGraphIso
    (source (graph core4056) (root 6) 2 2) DegreeOneSmallSpectrum1973.graph sourceMap4056=true := by decide +kernel
theorem fusedMap4056_checked : acceptsGraphIso
    (fused (graph core4056) (root 6) 2 2) DegreeOneSmallSpectrum946.graph fusedMap4056=true := by decide +kernel
theorem certified4056 : Certified (graph core4056) (root 6) 2 2 :=
  of_native_maps core4056 DegreeOneSmallSpectrum1973.graph DegreeOneSmallSpectrum946.graph
    sourceMap4056 fusedMap4056 sourceMap4056_checked fusedMap4056_checked
    DegreeTwoThreeFiniteComparisons.comparison4056
#print axioms sourceMap4056_checked
#print axioms fusedMap4056_checked
#print axioms certified4056
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

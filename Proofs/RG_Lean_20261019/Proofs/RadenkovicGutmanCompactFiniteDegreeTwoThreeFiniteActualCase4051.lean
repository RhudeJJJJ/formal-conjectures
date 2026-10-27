/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4051 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap4051 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,11,12,5,6,7,8,9,10] (sourceLabel 6 2 2 v)
def fusedMap4051 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4051_checked : acceptsGraphIso
    (source (graph core4051) (root 6) 2 2) DegreeOneSmallSpectrum1876.graph sourceMap4051=true := by decide +kernel
theorem fusedMap4051_checked : acceptsGraphIso
    (fused (graph core4051) (root 6) 2 2) DegreeOneSmallSpectrum880.graph fusedMap4051=true := by decide +kernel
theorem certified4051 : Certified (graph core4051) (root 6) 2 2 :=
  of_native_maps core4051 DegreeOneSmallSpectrum1876.graph DegreeOneSmallSpectrum880.graph
    sourceMap4051 fusedMap4051 sourceMap4051_checked fusedMap4051_checked
    DegreeTwoThreeFiniteComparisons.comparison4051
#print axioms sourceMap4051_checked
#print axioms fusedMap4051_checked
#print axioms certified4051
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4046 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap4046 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,12,6,7,8,9,10,11] (sourceLabel 6 2 2 v)
def fusedMap4046 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4046_checked : acceptsGraphIso
    (source (graph core4046) (root 6) 2 2) DegreeOneSmallSpectrum1438.graph sourceMap4046=true := by decide +kernel
theorem fusedMap4046_checked : acceptsGraphIso
    (fused (graph core4046) (root 6) 2 2) DegreeOneSmallSpectrum935.graph fusedMap4046=true := by decide +kernel
theorem certified4046 : Certified (graph core4046) (root 6) 2 2 :=
  of_native_maps core4046 DegreeOneSmallSpectrum1438.graph DegreeOneSmallSpectrum935.graph
    sourceMap4046 fusedMap4046 sourceMap4046_checked fusedMap4046_checked
    DegreeTwoThreeFiniteComparisons.comparison4046
#print axioms sourceMap4046_checked
#print axioms fusedMap4046_checked
#print axioms certified4046
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

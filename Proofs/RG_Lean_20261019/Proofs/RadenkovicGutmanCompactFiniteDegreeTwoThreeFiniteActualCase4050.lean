/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4050 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap4050 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,12,6,7,8,9,10,11] (sourceLabel 6 2 2 v)
def fusedMap4050 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4050_checked : acceptsGraphIso
    (source (graph core4050) (root 6) 2 2) DegreeOneSmallSpectrum1833.graph sourceMap4050=true := by decide +kernel
theorem fusedMap4050_checked : acceptsGraphIso
    (fused (graph core4050) (root 6) 2 2) DegreeOneSmallSpectrum873.graph fusedMap4050=true := by decide +kernel
theorem certified4050 : Certified (graph core4050) (root 6) 2 2 :=
  of_native_maps core4050 DegreeOneSmallSpectrum1833.graph DegreeOneSmallSpectrum873.graph
    sourceMap4050 fusedMap4050 sourceMap4050_checked fusedMap4050_checked
    DegreeTwoThreeFiniteComparisons.comparison4050
#print axioms sourceMap4050_checked
#print axioms fusedMap4050_checked
#print axioms certified4050
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

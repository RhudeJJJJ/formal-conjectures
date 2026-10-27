/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4052 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap4052 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,12,6,7,8,9,10,11] (sourceLabel 6 2 2 v)
def fusedMap4052 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4052_checked : acceptsGraphIso
    (source (graph core4052) (root 6) 2 2) DegreeOneSmallSpectrum1926.graph sourceMap4052=true := by decide +kernel
theorem fusedMap4052_checked : acceptsGraphIso
    (fused (graph core4052) (root 6) 2 2) DegreeOneSmallSpectrum910.graph fusedMap4052=true := by decide +kernel
theorem certified4052 : Certified (graph core4052) (root 6) 2 2 :=
  of_native_maps core4052 DegreeOneSmallSpectrum1926.graph DegreeOneSmallSpectrum910.graph
    sourceMap4052 fusedMap4052 sourceMap4052_checked fusedMap4052_checked
    DegreeTwoThreeFiniteComparisons.comparison4052
#print axioms sourceMap4052_checked
#print axioms fusedMap4052_checked
#print axioms certified4052
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

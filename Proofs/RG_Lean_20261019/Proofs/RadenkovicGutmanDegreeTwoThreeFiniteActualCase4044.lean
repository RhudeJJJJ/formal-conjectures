/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4044 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap4044 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,8,2,3,4,5,6,7] (sourceLabel 6 2 2 v)
def fusedMap4044 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4044_checked : acceptsGraphIso
    (source (graph core4044) (root 6) 2 2) DegreeOneSmallSpectrum1459.graph sourceMap4044=true := by decide +kernel
theorem fusedMap4044_checked : acceptsGraphIso
    (fused (graph core4044) (root 6) 2 2) DegreeOneSmallSpectrum860.graph fusedMap4044=true := by decide +kernel
theorem certified4044 : Certified (graph core4044) (root 6) 2 2 :=
  of_native_maps core4044 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum860.graph
    sourceMap4044 fusedMap4044 sourceMap4044_checked fusedMap4044_checked
    DegreeTwoThreeFiniteComparisons.comparison4044
#print axioms sourceMap4044_checked
#print axioms fusedMap4044_checked
#print axioms certified4044
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4038 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap4038 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,7,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap4038 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap4038_checked : acceptsGraphIso
    (source (graph core4038) (root 5) 2 2) DegreeOneSmallSpectrum561.graph sourceMap4038=true := by decide +kernel
theorem fusedMap4038_checked : acceptsGraphIso
    (fused (graph core4038) (root 5) 2 2) DegreeOneSmallSpectrum396.graph fusedMap4038=true := by decide +kernel
theorem certified4038 : Certified (graph core4038) (root 5) 2 2 :=
  of_native_maps core4038 DegreeOneSmallSpectrum561.graph DegreeOneSmallSpectrum396.graph
    sourceMap4038 fusedMap4038 sourceMap4038_checked fusedMap4038_checked
    DegreeTwoThreeFiniteComparisons.comparison4038
#print axioms sourceMap4038_checked
#print axioms fusedMap4038_checked
#print axioms certified4038
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4037 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap4037 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 4 2 2 v)
def fusedMap4037 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap4037_checked : acceptsGraphIso
    (source (graph core4037) (root 4) 2 2) DegreeOneSmallSpectrum348.graph sourceMap4037=true := by decide +kernel
theorem fusedMap4037_checked : acceptsGraphIso
    (fused (graph core4037) (root 4) 2 2) DegreeOneSmallSpectrum202.graph fusedMap4037=true := by decide +kernel
theorem certified4037 : Certified (graph core4037) (root 4) 2 2 :=
  of_native_maps core4037 DegreeOneSmallSpectrum348.graph DegreeOneSmallSpectrum202.graph
    sourceMap4037 fusedMap4037 sourceMap4037_checked fusedMap4037_checked
    DegreeTwoThreeFiniteComparisons.comparison4037
#print axioms sourceMap4037_checked
#print axioms fusedMap4037_checked
#print axioms certified4037
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

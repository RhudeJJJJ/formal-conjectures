/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3751 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3751 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![4,0,1,2,3,9,5,6,7,8] (sourceLabel 5 1 1 v)
def fusedMap3751 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap3751_checked : acceptsGraphIso
    (source (graph core3751) (root 5) 1 1) DegreeOneSmallSpectrum123.graph sourceMap3751=true := by decide +kernel
theorem fusedMap3751_checked : acceptsGraphIso
    (fused (graph core3751) (root 5) 1 1) DegreeOneSmallSpectrum076.graph fusedMap3751=true := by decide +kernel
theorem certified3751 : Certified (graph core3751) (root 5) 1 1 :=
  of_native_maps core3751 DegreeOneSmallSpectrum123.graph DegreeOneSmallSpectrum076.graph
    sourceMap3751 fusedMap3751 sourceMap3751_checked fusedMap3751_checked
    DegreeTwoThreeFiniteComparisons.comparison3751
#print axioms sourceMap3751_checked
#print axioms fusedMap3751_checked
#print axioms certified3751
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

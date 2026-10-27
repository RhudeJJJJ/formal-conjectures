/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4048 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap4048 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,9,10,11,12,7,8,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap4048 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4048_checked : acceptsGraphIso
    (source (graph core4048) (root 6) 2 2) DegreeOneSmallSpectrum1456.graph sourceMap4048=true := by decide +kernel
theorem fusedMap4048_checked : acceptsGraphIso
    (fused (graph core4048) (root 6) 2 2) DegreeOneSmallSpectrum971.graph fusedMap4048=true := by decide +kernel
theorem certified4048 : Certified (graph core4048) (root 6) 2 2 :=
  of_native_maps core4048 DegreeOneSmallSpectrum1456.graph DegreeOneSmallSpectrum971.graph
    sourceMap4048 fusedMap4048 sourceMap4048_checked fusedMap4048_checked
    DegreeTwoThreeFiniteComparisons.comparison4048
#print axioms sourceMap4048_checked
#print axioms fusedMap4048_checked
#print axioms certified4048
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

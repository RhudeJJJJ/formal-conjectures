/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2048 : Family 10 := level10.get ⟨411,by decide⟩
def sourceMap2048 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2048 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2048_checked : acceptsGraphIso
    (source (graph core2048) (root 10) 0 0) DegreeOneSmallSpectrum1100.graph sourceMap2048=true := by decide +kernel
theorem fusedMap2048_checked : acceptsGraphIso
    (fused (graph core2048) (root 10) 0 0) DegreeOneSmallSpectrum1489.graph fusedMap2048=true := by decide +kernel
theorem certified2048 : Certified (graph core2048) (root 10) 0 0 :=
  of_native_maps core2048 DegreeOneSmallSpectrum1100.graph DegreeOneSmallSpectrum1489.graph
    sourceMap2048 fusedMap2048 sourceMap2048_checked fusedMap2048_checked
    DegreeOneSmallComparisons.comparison2048
#print axioms sourceMap2048_checked
#print axioms fusedMap2048_checked
#print axioms certified2048
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2447 : Family 10 := level10.get ⟨1420,by decide⟩
def sourceMap2447 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,10,11,12,1,2,3,4,8,9,6,7] (sourceLabel 10 0 0 v)
def fusedMap2447 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2447_checked : acceptsGraphIso
    (source (graph core2447) (root 10) 0 0) DegreeOneSmallSpectrum1605.graph sourceMap2447=true := by decide +kernel
theorem fusedMap2447_checked : acceptsGraphIso
    (fused (graph core2447) (root 10) 0 0) DegreeOneSmallSpectrum1978.graph fusedMap2447=true := by decide +kernel
theorem certified2447 : Certified (graph core2447) (root 10) 0 0 :=
  of_native_maps core2447 DegreeOneSmallSpectrum1605.graph DegreeOneSmallSpectrum1978.graph
    sourceMap2447 fusedMap2447 sourceMap2447_checked fusedMap2447_checked
    DegreeOneSmallComparisons.comparison2447
#print axioms sourceMap2447_checked
#print axioms fusedMap2447_checked
#print axioms certified2447
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

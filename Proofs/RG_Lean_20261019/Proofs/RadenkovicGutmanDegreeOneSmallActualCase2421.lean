/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2421 : Family 10 := level10.get ⟨1306,by decide⟩
def sourceMap2421 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2421 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2421_checked : acceptsGraphIso
    (source (graph core2421) (root 10) 0 0) DegreeOneSmallSpectrum1718.graph sourceMap2421=true := by decide +kernel
theorem fusedMap2421_checked : acceptsGraphIso
    (fused (graph core2421) (root 10) 0 0) DegreeOneSmallSpectrum1943.graph fusedMap2421=true := by decide +kernel
theorem certified2421 : Certified (graph core2421) (root 10) 0 0 :=
  of_native_maps core2421 DegreeOneSmallSpectrum1718.graph DegreeOneSmallSpectrum1943.graph
    sourceMap2421 fusedMap2421 sourceMap2421_checked fusedMap2421_checked
    DegreeOneSmallComparisons.comparison2421
#print axioms sourceMap2421_checked
#print axioms fusedMap2421_checked
#print axioms certified2421
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

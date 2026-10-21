/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2319 : Family 10 := level10.get ⟨1010,by decide⟩
def sourceMap2319 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2319 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2319_checked : acceptsGraphIso
    (source (graph core2319) (root 10) 0 0) DegreeOneSmallSpectrum1564.graph sourceMap2319=true := by decide +kernel
theorem fusedMap2319_checked : acceptsGraphIso
    (fused (graph core2319) (root 10) 0 0) DegreeOneSmallSpectrum1568.graph fusedMap2319=true := by decide +kernel
theorem certified2319 : Certified (graph core2319) (root 10) 0 0 :=
  of_native_maps core2319 DegreeOneSmallSpectrum1564.graph DegreeOneSmallSpectrum1568.graph
    sourceMap2319 fusedMap2319 sourceMap2319_checked fusedMap2319_checked
    DegreeOneSmallComparisons.comparison2319
#print axioms sourceMap2319_checked
#print axioms fusedMap2319_checked
#print axioms certified2319
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

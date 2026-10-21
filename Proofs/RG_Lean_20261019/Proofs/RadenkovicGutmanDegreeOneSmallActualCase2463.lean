/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2463 : Family 10 := level10.get ⟨1542,by decide⟩
def sourceMap2463 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2463 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2463_checked : acceptsGraphIso
    (source (graph core2463) (root 10) 0 0) DegreeOneSmallSpectrum1998.graph sourceMap2463=true := by decide +kernel
theorem fusedMap2463_checked : acceptsGraphIso
    (fused (graph core2463) (root 10) 0 0) DegreeOneSmallSpectrum1554.graph fusedMap2463=true := by decide +kernel
theorem certified2463 : Certified (graph core2463) (root 10) 0 0 :=
  of_native_maps core2463 DegreeOneSmallSpectrum1998.graph DegreeOneSmallSpectrum1554.graph
    sourceMap2463 fusedMap2463 sourceMap2463_checked fusedMap2463_checked
    DegreeOneSmallComparisons.comparison2463
#print axioms sourceMap2463_checked
#print axioms fusedMap2463_checked
#print axioms certified2463
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

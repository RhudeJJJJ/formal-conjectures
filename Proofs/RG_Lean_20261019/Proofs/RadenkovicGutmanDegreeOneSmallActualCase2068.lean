/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2068 : Family 10 := level10.get ⟨448,by decide⟩
def sourceMap2068 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2068 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2068_checked : acceptsGraphIso
    (source (graph core2068) (root 10) 0 0) DegreeOneSmallSpectrum1143.graph sourceMap2068=true := by decide +kernel
theorem fusedMap2068_checked : acceptsGraphIso
    (fused (graph core2068) (root 10) 0 0) DegreeOneSmallSpectrum1507.graph fusedMap2068=true := by decide +kernel
theorem certified2068 : Certified (graph core2068) (root 10) 0 0 :=
  of_native_maps core2068 DegreeOneSmallSpectrum1143.graph DegreeOneSmallSpectrum1507.graph
    sourceMap2068 fusedMap2068 sourceMap2068_checked fusedMap2068_checked
    DegreeOneSmallComparisons.comparison2068
#print axioms sourceMap2068_checked
#print axioms fusedMap2068_checked
#print axioms certified2068
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

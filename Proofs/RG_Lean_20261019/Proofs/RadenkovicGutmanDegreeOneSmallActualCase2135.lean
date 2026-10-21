/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2135 : Family 10 := level10.get ⟨579,by decide⟩
def sourceMap2135 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2135 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2135_checked : acceptsGraphIso
    (source (graph core2135) (root 10) 0 0) DegreeOneSmallSpectrum1785.graph sourceMap2135=true := by decide +kernel
theorem fusedMap2135_checked : acceptsGraphIso
    (fused (graph core2135) (root 10) 0 0) DegreeOneSmallSpectrum1117.graph fusedMap2135=true := by decide +kernel
theorem certified2135 : Certified (graph core2135) (root 10) 0 0 :=
  of_native_maps core2135 DegreeOneSmallSpectrum1785.graph DegreeOneSmallSpectrum1117.graph
    sourceMap2135 fusedMap2135 sourceMap2135_checked fusedMap2135_checked
    DegreeOneSmallComparisons.comparison2135
#print axioms sourceMap2135_checked
#print axioms fusedMap2135_checked
#print axioms certified2135
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

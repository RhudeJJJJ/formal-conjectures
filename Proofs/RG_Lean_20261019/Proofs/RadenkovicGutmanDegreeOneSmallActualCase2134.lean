/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2134 : Family 10 := level10.get ⟨578,by decide⟩
def sourceMap2134 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2134 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2134_checked : acceptsGraphIso
    (source (graph core2134) (root 10) 0 0) DegreeOneSmallSpectrum1786.graph sourceMap2134=true := by decide +kernel
theorem fusedMap2134_checked : acceptsGraphIso
    (fused (graph core2134) (root 10) 0 0) DegreeOneSmallSpectrum1114.graph fusedMap2134=true := by decide +kernel
theorem certified2134 : Certified (graph core2134) (root 10) 0 0 :=
  of_native_maps core2134 DegreeOneSmallSpectrum1786.graph DegreeOneSmallSpectrum1114.graph
    sourceMap2134 fusedMap2134 sourceMap2134_checked fusedMap2134_checked
    DegreeOneSmallComparisons.comparison2134
#print axioms sourceMap2134_checked
#print axioms fusedMap2134_checked
#print axioms certified2134
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
